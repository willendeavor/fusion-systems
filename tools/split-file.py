# Program that given a fusion system file saved via the legacy SaveFS splits it into one 
# file per fusion system. Used to convert the old database to the SmallFusionSystems one



import os


pairs = [[2,3], [2,4], [2,5], [2,6], [2,7],
		[3,3], [3,4], [3,5], [3,6],
		[5,3], [5,4], [5,5], 
		[7,3], [7,4], [7,5]
		]



def CreateFiles(input_file, output_dir):
	os.makedirs(output_dir, exist_ok = True)
	fusion_systems = []
	with open(input_file) as f:
		lines = f.read().splitlines()
		new_fs = [i for i, line in enumerate(lines) if line.startswith("S:=")]
		end_fs = [i for i, line in enumerate(lines) if line.startswith("FS:=")]

	for i in range(len(new_fs)):
		fname = os.path.join(output_dir, f"FS_{i + 1}.m")
		with open(fname, "w") as out:
			out.write("\n".join(lines[new_fs[i]:end_fs[i]+1]))



filelist = ["OLD/All5to6/" + x for x in os.listdir("OLD/All5to6")]

for f in filelist:
	CreateFiles(f, "5to6")