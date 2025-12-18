# Reflects name changes in the attributes of a record
import re
from pathlib import Path

ATTR_MAP = {
    "Core": "core",
    "FocalSubgroup": "focal_subgroup",
    "OpTriv": "core_trivial",
    "FusionGroup" : "fusion_group",
    "FusionGroup_name" : "fusion_group_name"
}

ROOT = Path("SmallFusionSystems")  # adjust if needed

def rewrite_file(path: Path):
    text = path.read_text()

    original = text

    for old, new in ATTR_MAP.items():
        # R`Core  → R`core
        text = re.sub(rf"`{old}\b", f"`{new}", text)

        # Core :=  → core :=
        text = re.sub(rf"\b{old}\s*:=", f"{new} :=", text)

        text = re.sub(
            rf"\b{old}\s*:",
            f"{new} :",
            text
        )
    if text != original:
        path.write_text(text)
        print(f"Updated {path}")

def main():
    for fs_file in ROOT.rglob("FS_*.m"):
        rewrite_file(fs_file)

if __name__ == "__main__":
    main()