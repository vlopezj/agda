#!/usr/bin/python3

import os
import sys
import re
from collections import defaultdict

def read_times(dir):
    result = defaultdict(lambda: defaultdict(lambda: dict()))
    for file in os.listdir(dir):
        m = re.match(r"^(.*)\.(\d+).time$", file)
        if m:
            variant = m.group(1)
            size = int(m.group(2))
            rf = read_times_file(dir + "/" + file)
            for module, time in rf.items():
                result[variant][module][size] = time
        else:
            print('Invalid filename: ' + file, file = sys.stderr)
    return result

def read_times_file(path):
    result = {}
    with open(path) as f:
        for line in f:
            m = re.match(r"^(.*?)[ \t]*([0-9,.]+)ms$", line)
            if m:
                result[m.group(1)] = int(re.sub(r"[^0-9]",'',m.group(2)))
            elif not re.match(r"^[^ ]*$", line): 
                print('Invalid line ' + line + ' in filename ' + path, file = sys.stderr) 
    return result
