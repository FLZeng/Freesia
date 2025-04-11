# Freesia: Verifying Correctness of TEE Communication with Concurrent Separation Logic

## 1 Artifact Description

This is the artifact for the ISSTA 2025 paper *Freesia: Verifying Correctness of TEE Communication with Concurrent Separation Logic*. The artifact includes the source code of *Freesia* prototype, the model and proofs of *Freesia*, and evaluation results. The directory structure is as follows:

```
|-- Freesia
    |-- Freesia_model               # Freesia formal model and proofs in Iris
    |-- Freesia_prototype           # Freesia prototype in OP-TEE
        |-- patches
            |-- apply_patches.sh    # scripts for applying patches
            |-- revert_patches.sh   # scripts for reverting patches
            |-- xxx.patch           # patches of OP-TEE components
        |-- common.xml              # manifest specifing the revision of OP-TEE components
        |-- qemu_v8.xml             # manifest specifing the revision of dependencies
    |-- results                     # evaluation results data
```

For ease of artifact evaluation and usage, we also provide a virtual machine image in qcow2 format.

## 2 Environment Setup

The environment can be a physical or virtual machine in the following minimal configuration:

- OS: Ubuntu 23.10 with GUI
- CPU: 8-core AMD EPYC 9654 CPU @ 2.4GHz
- RAM: 8GB
- Disk: 50GB

Notes:

- The GUI must be installed on the Ubuntu because OP-TEE starts xterm when it runs.
- For faster compilation, we recommend a processor with 8 cores or more.

### 2.1 Pre-configured VM image

A configured virtual machine image is provided and can be downloaded from: https://zenodo.org/record/15181173/files/freesia-ae.qcow2

Create a VM with `virt-manager` (or `virt-install` command line) that meets the minimum configuration requirements and use the provided image as the disk for the VM. To create a virtual machine with `virt-install`:

```
virt-install \
  --virt-type kvm \
  --name freesia-ae \
  --vcpus 8 \
  --ram 8192 \
  --disk path=/PATH/TO/freesia-ae.qcow2 \
  --os-variant ubuntu23.10 \
  --import \
  --autostart \
  --noautoconsole
```

Or you can convert the image to another format to run on VMWare Workstation (vmdk) or VirtualBox (vdi).

The username for the VM is `root` and password is `123456`.

This README file exists on the desktop of the `root` user of the VM.

## 3 Getting Started

You can start from scratch or use the provided VM image.

If you are using the provided VM image, the first 5 steps below are not required and you can skip to the **3.6 Compile and run** step.

The following commands can be executed in the ssh text interface, but remember to log into the GUI with the same user first.

### 3.1 Install dependency packages

```
# apt install adb acpica-tools autoconf automake bc bison \
    build-essential ccache cpio cscope curl device-tree-compiler \
    e2tools expect fastboot flex ftp-upload gdisk git libattr1-dev \
    libcap-ng-dev libfdt-dev libftdi-dev libglib2.0-dev libgmp3-dev \
    libhidapi-dev libmpc-dev libncurses5-dev libpixman-1-dev \
    libslirp-dev libssl-dev libtool libusb-1.0-0-dev make mtools netcat-openbsd \
    ninja-build python3-cryptography python3-pip python3-pyelftools \
    python3-serial python-is-python3 rsync swig unzip uuid-dev wget \
    xalan xdg-utils xterm xz-utils zlib1g-dev

# curl https://storage.googleapis.com/git-repo-downloads/repo > /bin/repo && chmod a+x /bin/repo
```

### 3.2 Get Freesia project

Unzip the artifact archive and get a directory named *Freesia*. Or you can clone *Freesia* from the repository:

```
# export FREESIA_DIR="/data/Freesia"
# mkdir /data
# git clone https://github.com/FLZeng/Freesia.git ${FREESIA_DIR}
```

### 3.3 Sync OP-TEE source code

```
# cd ${FREESIA_DIR}/Freesia_prototype
# repo init -u https://github.com/OP-TEE/manifest.git -m qemu_v8.xml
# cp common.xml .repo/manifests/common.xml
# cp qemu_v8.xml .repo/manifests/qemu_v8.xml
# repo sync
```

### 3.4 Download toolchains

```
# cd ${FREESIA_DIR}/Freesia_prototype/build
# make toolchains -j2
```

Add Cargo's bin directory in the PATH environment variable:
```
# export PATH="${FREESIA_DIR}/Freesia_prototype/build/../toolchains/rust/.cargo/bin:$PATH"
```

### 3.5 Apply Freesia pathes

```
# cd ${FREESIA_DIR}/Freesia_prototype
# sh patches/apply_patches.sh
```

### 3.6 Compile and run

To enable build as root:
```
# export FORCE_UNSAFE_CONFIGURE=1
```

Build and run:
```
# cd ${FREESIA_DIR}/Freesia_prototype/build
# make clean
# KCFLAGS="-march=armv8.5-a+memtag" make MEMTAG=y run -j$(nproc)
```

Once the compilation is complete, a QEMU VM will be launched to run OP-TEE. When you see the following message, type a `c` and `enter`:

```
cd ../out/bin && ../qemu/build/aarch64-softmmu/qemu-system-aarch64 \
        -nographic -smp 2 -cpu max,sme=on,pauth-impdef=on -d unimp \
        -semihosting-config enable=on,target=native -m 1057 \
        -bios bl1.bin -initrd rootfs.cpio.gz -kernel Image \
        -append 'console=ttyAMA0,38400 keep_bootcon root=/dev/vda2 ' \
        -object rng-random,filename=/dev/urandom,id=rng0 \
        -device virtio-rng-pci,rng=rng0,max-bytes=1024,period=1000 \
        -netdev user,id=vmnic -device virtio-net-device,netdev=vmnic \
        -machine virt,acpi=off,secure=on,mte=on,gic-version=3,virtualization=false  \
        -s -S -serial tcp:127.0.0.1:54320 -serial tcp:127.0.0.1:54321
QEMU 8.1.2 monitor - type 'help' for more information
(qemu) 
```

Then in the GUI, you can see that two xterms are launched, one for the Normal World and the other for the Secure World.

When the following prompt appears in the normal world terminal, enter root to log in without a password:

```
Welcome to Buildroot, type root or test to login
buildroot login:
```

**Note**: whenever you change the compilation parameters, the legacy output files may cause compilation failure. Execute the following command to clean the compilation environment:

```
# make clean
# rm -rf ${FREESIA_DIR}/Freesia_prototype/out ${FREESIA_DIR}/Freesia_prototype/out-br
```

### 3.8 Examine basic functionality

Run the test application in the normal world terminal:

```
# optee_example_shared_mem
```

*optee_example_shared_mem* accepts the following input commands:

- 1: test normal access on tmpref sequentially
- 2: test memory access violation on tmpref concurrently
- 3: test memory access violation on allocated memref
- 4: test memory access violation on registered memref
- 5: test performance
- q: quit

Input `1`~`4` for functionality tests. The cases `2`, `3`, and `4` would end up *SIGSEGV*, since memory access violation is deliberately triggered in these testcases.

```
# optee_example_shared_mem
[1] - test tmpref sequentially
[2] - test tmpref concurrently
[3] - test allocated memref
[4] - test registered memref
[5] - evaluate performance
[q] - quit
waiting for cmd [0/1/2/3/4/5/6/q]: 2
Call malloc to allocate buffer
Allocated buffer: (0xaaab0709f2f0)[8224]
Call TEEC_InitializeContext
Call TEEC_OpenSession
Invoking TA to increment buf[0]: 42
Incrementing buf[0] in CA
Expecting SIGSEGV...
Segmentation fault
```

The detailed evaluation experiments are described in the next section.

## 4 Detailed Description

The evaluation experiments include microbenchmarks, TA Benchmarks, multi-thread TA Performance, and Locking Mechanisms Comparison. The following commands are all executed in the normal world terminal.

The [`results/`](results/) directory contains all the experimental results data, which can be reproduced as follows.

### 4.1 Microbenchmarks

The original data are in `TEE_Communication_API.csv` and averaged in `TEE_Communication_API_Averaged.csv` for statistical purposes.

To reproduce the results, run:

```
# optee_example_shared_mem
```

then input `5` to measure the execution `time (μs)` of each TEE communication interfaces.

### 4.2 TA Benchmarks

The performance of **SHA256**, **AES-256**, **RSASSA-PSS**, and **Secure Storage** are tested under different buffer sizes. For all TAs, the values of `BUFFER_SIZE` are: 256, 4096, and 65536 in Byte.

The original data are in `TA_Performance.csv` and  averaged in `TA_Performance_Averaged.csv` for statistical purposes. TAs are evaluated as follows. 

**SHA256**

```
# for i in $(seq 1 10); do xtest --sha-perf -r -n 1000 -a SHA256 -s BUFFER_SIZE; done
```

Take the `mean time (μs)` in the result.

**AES-256-gcm encryption**

```
# for i in $(seq 1 10); do xtest --aes-perf -r -n 1000 -k 256 -s BUFFER_SIZE; done
```

Take the `mean time (μs)` in the result.

**Asym RSASSA-PSS**

```
# xtest --asym-perf -a RSASSA_PKCS1_PSS_MGF1_SHA256_SIGN -r -k BUFFER_SIZE
```

Take the `mean time (μs)` in the result.

**Secure Storage**

```
# xtest -t benchmark 1001 1002
```

Take the `Speed (kB/s)` in the result.

### 4.3 TEE Concurrency Benchmarks

The original data are in `TEE_Concurrency.csv` and averaged in `TEE_Concurrency_Averaged.csv` for statistical purposes.

Run the following command with specific `NUM_THREADS` and `REPEAT` to measure the concurrency under different client threads:

```
# for i in $(seq 1 10); do echo "1 NUM_THREADS REPEAT" | optee_example_perf_concurrency; done
```

In our experiments, the `REPEAT` is 100 and the `NUM_THREADS` ranges from 1 to 128. Take the `Mean read concurrency` as the result.

### 4.4 Locking Mechanisms Comparison

The original data are in `Locking_Mechanisms_Memory.csv` and `Locking_Mechanisms_Time.csv`, with averaged data in `Locking_Mechanisms_Memory_Averaged.csv` and `Locking_Mechanisms_Time_Averaged.csv` for statistical purposes.

Run the following command with specific `NUM_THREADS` to measure the concurrency under different client threads:

```
# for i in $(seq 1 10); do echo "4 NUM_THREADS" | optee_example_perf_concurrency; done
```
In our experiments, the `NUM_THREADS` ranges from 1 to 128. Take the `Mutex mem bytes` and `Avg thread exec ms` as the result.

To measure different locking mechanisms, cd `optee_client/libteec/src/` and replace `tee_client_api.c` with one of the follwing implementations:
- global lock: `tee_client_api_global.c`
- per-type lock: `tee_client_api_per_type.c`
- per-object lock: `tee_client_api_per_object.c`
- mutex pool: `tee_client_api_pool.c`

Then redo the **3.6 Compile and run** and subsequent steps.

### 4.5 Reproduction of concurrent vulnerability

Note that in order to trigger this vulnerability, the `MTE` must be disabled.

Modify the relevant functions in `linux/arch/arm64/include/asm/uaccess.h` as follows:

```c
#define insert_random_tag(ptr) (ptr)
#define set_tag(tagged_addr) do { } while (0)
#define get_tag(tagged_addr) ((tagged_addr) & (0xful << 56))
#define clear_tag(tagged_addr)
```

And recompile the project without `MTE option`:

```
# make clean
# make run -j$(nproc)
```

otherwise *double free* in the PTA will cause the Trusted OS to crash.

Then run the following command in the normal world console:

```
# optee_example_heap_vuln
```

You are expected to see the following message in the output, indicating that the attacker has stolen the secret:

```
Secret: TOPSECRETTOPSECRETTOPSECRET
```

### 4.6 Normalization

For each test, obtain the results in native OP-TEE (`a`) and  *Freesia* (`b`) separately, and then take `b/a` as the normalized value.

Execute the following commands to restore the native OP-TEE environment:

```
# cd ${FREESIA_DIR}/Freesia_prototype
# sh patches/revert_patches.sh
# sh patches/apply_app_patches.sh
```

Then redo the **3.6 Compile and run** and subsequent steps.
