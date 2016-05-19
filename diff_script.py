import sys
import subprocess
import os.path

def get_fname(crashes,sent):
	return 'schedules/Schedule_k'+str(crashes)+'_l'+str(sent)

def diff_script(k,l):
	flag = False
	differed_l = []

	if os.path.isfile(get_fname(k,l)):
		flag = True

	while True:
		if os.path.isfile(get_fname(k,l)) and os.path.isfile(get_fname(k,l+1)):
			# print "Comparing {},{} with {},{}".format(k,l,k,l+1)
			cmd = 'diff '+ get_fname(k,l) + ' ' + get_fname(k,l+1) + ' >/dev/null'
			if subprocess.call(cmd ,shell=True) != 1:
				print "{},{} and {},{} same".format(str(k),str(l),str(k),str(l+1))
			else:
				print "{},{} and {},{} DIFFER!".format(str(k),str(l),str(k),str(l+1))
				differed_l.append(l)
		else:
			break
		l += 1

	if not flag:
		return None
	else:
		return differed_l