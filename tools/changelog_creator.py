# Given two data directories compares them and creates a changelog of sorts



import glob, re, datetime

# E.g. root = "data_old"
def GetCount(root):
	count = {}
	# Get a list of [p,n] pairs
	pn_paths = glob.glob(root + "/**/p_*/n_*", recursive = True)
	pn = []
	for path in pn_paths:
		x = re.search(r"p_(\d+)\\n_(\d+)", path)
		pn.append((x.group(1), x.group(2)))

	# For each pair get the number of fusion systems
	for pair in pn:
		p = pair[0]
		n = pair[1]
		filename = "FS_p" + str(p) + "_n" + str(n) + "*.m"
		m = len(glob.glob(root + "/**/" + filename, recursive = True))
		count[pair] = m
	return(count)


def GetUpdateLog(root):
	path = glob.glob(root + "/**/update.log", recursive = True)[0]
	with open(path) as f:
		lines = [line.rstrip("\n") for line in f]
	return(lines)


old_count = GetCount("data_old")
new_count = GetCount("data_new")

log_old = GetUpdateLog("data_old")
log_new = GetUpdateLog("data_new")

old_total = sum(old_count.values())
new_total = sum(new_count.values())

new_id = f"v{new_total}_u{len(log_new)}"
old_id = f"v{old_total}_u{len(log_old)}"


# Start making the file
lines = []
lines.append(f"dataset_id : {new_id}")
lines.append(f"previous_dataset_id : {old_id}")
lines.append(f"date_created : {str(datetime.datetime.now())}")

lines.append(f"update log new entries : {len(log_new) - len(log_old)}")

lines.append("Totals: ")
lines.append(f"  old : {old_total}")
lines.append(f"  new : {new_total}")
lines.append(f"  diff : {new_total - old_total}")


lines.append("(p,n) totals: ")
for pair in new_count:
	pn = f"  ({pair[0]}, {pair[1]}) : "
	if not pair in old_count:
		pn = pn + f"0 -> {new_count[pair]} (+{new_count[pair]})"
	else:
		pn = pn + f"{old_count[pair]} -> {new_count[pair]} (+{new_count[pair] - old_count[pair]})"
	lines.append(pn)


with open(f"/data_new/data_summary_{new_id}.info", "a") as f:
	for line in lines:
		f.write(line)
		f.write("\n")


with open(f"/data_new/changes_{new_id}.info", "a") as f:
	for line in log_new[len(log_old):]:
		f.write(line)
		f.write("\n")


