# Freesia: Verifying Correctness of TEE Communication with Concurrent Separation Logic

## 1 Artifact Description

The artifact of the *Freesia paper* includes the source code of *Freesia* prototype, the model and proofs of *Freesia*, and evaluation results. The directory structure is as follows:

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

## 2 Environment Setup

The environment can be a physical or virtual machine in the following minimal configuration:

- OS: Ubuntu 23.10 with GUI
- CPU: 4-core AMD EPYC 9654 CPU @ 2.4GHz
- RAM: 4GB
- Disk: 30GB

Notes:

- The GUI must be installed on the Ubuntu because OP-TEE starts xterm when it runs.
- For faster compilation, we recommend a processor with 8 cores or more.

## 3 Getting Started

The following commands can be executed in the ssh text interface, but remember to log into the GUI with the same user first.

### 3.1 Install dependency packages

```
# apt install adb acpica-tools autoconf automake bc bison \
    build-essential ccache cpio cscope curl device-tree-compiler \
    e2tools expect fastboot flex ftp-upload gdisk git libattr1-dev \
    libcap-ng-dev libfdt-dev libftdi-dev libglib2.0-dev libgmp3-dev \
    libhidapi-dev libmpc-dev libncurses5-dev libpixman-1-dev \
    libslirp-dev libssl-dev libtool libusb-1.0-0-dev make mtools netcat \
    ninja-build python3-cryptography python3-pip python3-pyelftools \
    python3-serial python-is-python3 rsync swig unzip uuid-dev wget \
    xalan xdg-utils xterm xz-utils zlib1g-dev

# curl https://storage.googleapis.com/git-repo-downloads/repo > /bin/repo && chmod a+x /bin/repo
```

### 3.2 Unzip the data

Unzip the artifact archive and get a directory named *Freesia*.

### 3.3 Sync OP-TEE source code

```
# cd Freesia/Freesia_prototype
# repo init -u https://github.com/OP-TEE/manifest.git -m qemu_v8.xml
# cp common.xml .repo/manifests/common.xml
# cp qemu_v8.xml .repo/manifests/qemu_v8.xml
# repo sync
```

### 3.4 Download toolchains

```
# cd build
# make toolchains -j2
```

### 3.5 Apply Freesia pathes

```
# cd ..
# sh patches/apply_patches.sh
```

### 3.6 Compile and run

```
# cd build
# KCFLAGS="-march=armv8.5-a+memtag" make MEMTAG=y run -j$(nproc)
```

Once the compilation is complete, a QEMU VM will be launched to run OP-TEE. When you see the following message, type a `c` and `enter`:

```
cd ../out/bin && ../qemu/build/aarch64-softmmu/qemu-system-aarch64 \
        -nographic -smp 2 -cpu max,sme=on,pauth-impdef=on -d unimp -semihosting-config enable=on,target=native -m 1057 -bios bl1.bin -initrd rootfs.cpio.gz -kernel Image -append 'console=ttyAMA0,38400 keep_bootcon root=/dev/vda2 '  -object rng-random,filename=/dev/urandom,id=rng0 -device virtio-rng-pci,rng=rng0,max-bytes=1024,period=1000 -netdev user,id=vmnic -device virtio-net-device,netdev=vmnic -machine virt,acpi=off,secure=on,mte=on,gic-version=3,virtualization=false   -s -S -serial tcp:127.0.0.1:54320 -serial tcp:127.0.0.1:54321
QEMU 8.1.2 monitor - type 'help' for more information
(qemu) 
```

Then in the GUI, you can see that two xterms are launched, one for normal world and the other for secure world.

When the following prompt appears in the normal world terminal, enter root to log in without a password:

```
Welcome to Buildroot, type root or test to login
buildroot login:
```

### 3.8 Examine basic functionality

Execute `xtest` to examine basic functionality by the test suite provided by optee.

You should get the following output after finishing the test:

```
+-----------------------------------------------------
39294 subtests of which 0 failed
138 test cases of which 0 failed
0 test cases were skipped
TEE test application done!
```

For functionality test of the shared memory, run:

```
# optee_example_shared_mem
```

then input 0 to 5 according to the prompt. Note that most of the cases would end up SIGSEGV, since memory access violation is deliberately triggered in the testcases.

The detailed evaluation experiments are described in the next section.

## 4 Reproducibility Instructions

The evaluation experiments include microbenchmarks, TA Benchmarks, and multi-thread TA Performance. The following commands are all executed in the normal world terminal.

The [`results/`](results/) directory contains all the experimental results data, which can be reproduced as follows.

### 4.1 Microbenchmarks

The original data are in `TEE_Communication_API.csv` and averaged in `TEE_Communication_API_Averaged.csv` for statistical purposes.

To reproduce the results, run:

```
# optee_example_shared_mem
```

then input 6 according to the prompt and then press enter.

### 4.2 TA Benchmarks

The original data are in `TA_Performance.csv` and  averaged in `TA_Performance_Averaged.csv` for statistical purposes. TAs are tested as follows. 

#### 4.2.1 SHA256

```
# for i in $(seq 1 10); do xtest --sha-perf -r -n 1000 -a SHA256 -s 65536; done
```

#### 4.2.2 AES-256-gcm encryption

```
# for i in $(seq 1 10); do xtest --aes-perf -r -n 1000 -k 256 -s 65536; done
```

#### 4.2.2 Asym RSASSA-PSS

```
# xtest --asym-perf -a RSASSA_PKCS1_PSS_MGF1_SHA256_SIGN -r -k 256
```

#### 4.2.3 Secure Storage

```
# xtest -t benchmark 1001 1002 | awk -v OFS="\t" '{print $3,$5}'
```

### 4.3 TEE Concurrency Benchmarks

The original data are in `TEE_Concurrency.csv` and averaged in `TEE_Concurrency_Averaged.csv` for statistical purposes.

Run the following command to measure the concurrency under different mutex pool size and client threads:

```
# for i in $(seq 1 20); do echo "128 100" | optee_example_perf_concurrency; done
```

### 4.4 Reproduction of concurrent vulnerability

To trigger double free in the `heap_vuln` PTA, run the following command in the normal world console:

```
optee_example_heap_vuln
```

### 4.5 Normalization

For each test, obtain the results in native OP-TEE (`a`) and  *Freesia* (`b`) separately, and then take `b/a` as the normalized value.

Execute the following commands to restore the native OP-TEE environment:

```
# cd Freesia_prototype
# sh patches/revert_patches.sh
```

Then redo the **compile and run** and subsequent steps.