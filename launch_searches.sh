INFILE=full_search_expansion.m.tpl
SCRATCH="_scratch_file"
OUTFILE_NAME=full_search_expansion

SEARCH_CASES=(
        "N=6;M=6;L=1;F=2"
        "N=6;M=6;L=2;F=2"
        "N=6;M=3;L=3;F=2"
        "N=6;M=3;L=4;F=2"
        "N=6;M=6;L=1;F=10"
        "N=6;M=6;L=2;F=10"
        "N=6;M=3;L=3;F=10"
        "N=6;M=2;L=4;F=10"
        "N=6;M=1;L=5;F=10"
        "N=8;M=8;L=1;F=2"
        "N=8;M=2;L=2;F=2"
        "N=8;M=2;L=3;F=2"
        "N=8;M=8;L=1;F=4"
        "N=8;M=4;L=2;F=4"
        "N=8;M=2;L=3;F=4"
        "N=8;M=1;L=4;F=4"
        "N=8;M=1;L=5;F=4"
        "N=8;M=8;L=1;F=28"
        "N=8;M=4;L=2;F=28"
        "N=8;M=2;L=3;F=28"
        "N=8;M=2;L=4;F=28"
        "N=8;M=8;L=1;F=82"
        "N=8;M=4;L=2;F=82"
        "N=8;M=2;L=3;F=82"
        "N=8;M=1;L=4;F=82"
        "N=8;M=1;L=5;F=82"
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