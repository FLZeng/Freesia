#!/usr/bin/env bash

PATCH_DIR="$(cd $(dirname $0);pwd)"
BASE_DIR="$(dirname $PATCH_DIR)"

PROJECTS="optee_examples optee_os"

for project in $(echo ${PROJECTS})
do
    echo "Applying patches for [${project}] ... "
    project_dir="${BASE_DIR}/${project}"
    patch_path="${PATCH_DIR}/${project}.patch"
    cd ${project_dir} && git restore --staged . && git restore . && git clean -fd && git apply ${patch_path}
    if [ $? -eq 0 ]; then
        echo "done"
    else
        echo ""
    fi
done
