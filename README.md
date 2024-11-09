# proofs-vote-share
A simple coq proof of a question that arose about voting in an election.

In order to view these files with the intended Coq parser, you should install:
- Visual Studio Code (1.94.2)
- VsCoq (v2.1.2)

You may find that Coq .v files can only be found by other Coq .v files when you've opened in Visual Studio Code the folder that directly contains that file (and not the parent folder) of multiple folders of .v files.

To build the project, locate the file called build_coq.sh and run it from the command line by typing "ctrl+'" and entering: ./build_coq.sh

Sometimes, the line endings aren't readable and you will first need to run: dos2unix build_coq.sh
