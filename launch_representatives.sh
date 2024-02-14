INFILE=full_search_f3m_representatives.m.tpl
SCRATCH="_scratch_file"
OUTFILE_NAME=full_search_expansion

SEARCH_CASES=(
        # "N=8;M=1;L=2;"
        "N=8;M=1;L=3;"
        "N=8;M=1;L=4;"
        "N=8;M=1;L=5;"
        "N=8;M=1;L=6;"
        "N=8;M=1;L=7;"
        "N=8;M=1;L=8;"
)

for SEARCH_CASE in ${SEARCH_CASES[@]}
do
        # Very sketchy but idc
        eval $SEARCH_CASE

        OUTFILE="_search_${SEARCH_CASE}.m"

        cp $INFILE $OUTFILE
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