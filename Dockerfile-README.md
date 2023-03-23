# Verif-IQC Docker Container

This repository contains the Dockerfile and instructions for the Verif-IQC Docker container, which provides a pre-configured environment for formal verification of invariants in control systems using Frama-C and Alt-Ergo-Poly.

## Pulling and Running the Docker Image

To pull the Docker image from Docker Hub and run it, follow these steps:

1. Install Docker on your machine. If you haven't already, you can follow the official installation guide for your operating system here: https://docs.docker.com/get-docker/

2. Open a terminal or command prompt on your machine.

3. Pull the Verif-IQC image from Docker Hub:

docker pull ekhalife/verif-iqc:latest

This command will download the Verif-IQC Docker image to your local machine.

4. Run a container using the pulled image:

docker run -it ekhalife/verif-iqc:latest

This will start a new container using the pulled Docker image and give you an interactive terminal.

(Depending on your system's configuration, you may need to add `sudo` before the docker pull and run commands, like this:
sudo docker pull ekhalife/verif-iqc:latest
sudo docker run -it ekhalife/verif-iqc:latest)

## Running Commands in the Container

Once inside the container, you should run the following commands before executing any other commands:

1. Initialize the OPAM environment:

eval $(opam env)

This command sets the required environment variables for the OPAM package manager, allowing you to properly use the installed tools, including Frama-C, Why3, and Alt-Ergo-Poly.

2. Run the Makefile:

make

The Makefile contains the necessary instructions to compile and run the formal verification process on the provided C files. Running `make` will execute the verification process using the pre-configured tools and settings.
