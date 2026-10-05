export PATH=$HOME/.elan/bin:$PATH; cd ~/simson; lake build 2>&1 | tail -60 > build.log; echo EXIT ${PIPESTATUS[0]} >> build.log
