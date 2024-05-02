INFILE=full_search_f3m_rep_mem.m.tpl
SCRATCH="_scratch_file"
OUTFILE_NAME=full_search_expansion

SEARCH_CASES=(
        # "P=3;N=8;M=1;L=2;"
        # "P=3;N=8;M=1;L=3;"
        # "P=3;N=8;M=1;L=4;"
        # "P=3;N=8;M=1;L=5;"
        # "P=3;N=8;M=1;L=6;"
        # "P=3;N=8;M=1;L=7;"
        # "P=3;N=8;M=1;L=8;"
        # "P=3;N=6;M=2;L=3;"
        # "P=3;N=6;M=2;L=4;"
        # "P=3;N=6;M=2;L=5;"
        # "P=3;N=6;M=2;L=6;"
        "P=3;N=10;M=1;L=3"
        # "P=3;N=10;M=1;L=4"
)

for SEARCH_CASE in ${SEARCH_CASES[@]}
do
        # Very sketchy but idc
        eval $SEARCH_CASE

        OUTFILE="_search_${SEARCH_CASE}.m"

        cp $INFILE $OUTFILE
        sed "s/@P@/${P}/g" $OUTFILE > $SCRATCH
        cp $SCRATCH $OUTFILE
        sed "s/@N@/${N}/g" $OUTFILE > $SCRATCH
        cp $SCRATCH $OUTFILE
        sed "s/@M@/${M}/g" $OUTFILE > $SCRATCH
        cp $SCRATCH $OUTFILE
        sed "s/@L@/${L}/g" $OUTFILE > $SCRATCH
        cp $SCRATCH $OUTFILE
        sed "s/@F@/${F}/g" $OUTFILE > $SCRATCH
        cp $SCRATCH $OUTFILE

        screen -dm magma $OUTFILE
done