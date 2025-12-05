import os


pairs = [[2,3], [2,4], [2,5], [2,6], [2,7],
		[3,3], [3,4], [3,5], [3,6],
		[5,3], [5,4], [5,5], 
		[7,3], [7,4], [7,5]
		]



def CreateFiles(p,n):
	input_file = "OLD/All" + str(p) + "to" + str(n)
	output_dir = "p_" + str(p) + "/n_" + str(n)
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

for pair in pairs:
	CreateFiles(pair[0], pair[1])

