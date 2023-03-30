#!/usr/bin/env bash

read_in () {
  while :
  do
    read input

    if [[ "$input" = "y" ]]; then
      return 0
    else
      if [[ "$input" = "n" ]]; then
        return 1
      else 
        echo "Invalid input. Please try again."
      fi
    fi
  done
}

echo "We will begin by setting up a new opam switch and a new conda env. Continue? [y/n]"

if read_in; then
    opam switch create synth coq=8.16.1
    conda create --name synth python=3.10.0
    eval $(opam env)
    conda activate synth
else
    echo "Exiting setup."
    exit 1
fi

echo "This setup script will clone a directory (proverbot9001-plugin) one level up from the current directory, and install a few dependencies from opam and pip. It will also download the pretrained weights that proverbot uses. Would you like to proceed with the setup [y/n]"


if read_in; then
    echo "Starting setup now, this may take a while."
    git clone git@github.com:agrarpan/proverbot9001-plugin.git ../proverbot9001-plugin
    cd ../proverbot9001-plugin
    make setup
    make download-weights
else
    echo "Exiting setup, no changes have been made to your current opam switch."
    exit 1
fi