#!/bin/bash

# Check if exactly one argument is provided
if [ "$#" -ne 1 ]; then
    echo "Usage: $0 <filename>"
    exit 1
fi

# Get the filename from the command line argument
filename="$1"

# Check if the file exists
if [ ! -f "$filename" ]; then
    echo "File not found: $filename"
    exit 1
fi

# Use sed to replace " sorry" with " sledgehammer"
sed -i 's/ sorry/ sledgehammer/g' "$filename"

echo "All occurrences of ' sorry' have been replaced with ' sledgehammer' in $filename."
	
