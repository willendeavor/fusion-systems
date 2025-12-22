# Script that renamed the files from FS_i to FS_pp_nn_i with padding

import os
import re

BASE_DIR = "SmallFusionSystems"
WIDTH = 5

# Matches FS_i or FS_i.sig
fs_pattern = re.compile(r"^FS_(\d+)(\.sig)?$")

# Matches p_<p>/n_<n>
p_dir_pattern = re.compile(r"^p_(\d+)$")
n_dir_pattern = re.compile(r"^n_(\d+)$")


def process_directory(dirpath, p, n):
    for filename in os.listdir(dirpath):
        m = fs_pattern.match(filename)
        if not m:
            continue

        i = int(m.group(1))
        ext = m.group(2)

        base = f"FS_p{p}_n{n}_{i:0{WIDTH}d}"

        if ext == ".sig":
            new_name = base + ".sig"
        else:
            new_name = base + ".m"

        old_path = os.path.join(dirpath, filename)
        new_path = os.path.join(dirpath, new_name)

        if old_path == new_path:
            continue

        print(f"{old_path} -> {new_path}")
        os.rename(old_path, new_path)


def main():
    for p_entry in os.listdir(BASE_DIR):
        p_match = p_dir_pattern.match(p_entry)
        if not p_match:
            continue

        p = int(p_match.group(1))
        p_path = os.path.join(BASE_DIR, p_entry)

        for n_entry in os.listdir(p_path):
            n_match = n_dir_pattern.match(n_entry)
            if not n_match:
                continue

            n = int(n_match.group(1))
            n_path = os.path.join(p_path, n_entry)

            process_directory(n_path, p, n)


if __name__ == "__main__":
    main()