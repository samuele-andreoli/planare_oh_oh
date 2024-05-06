INFILE=full_search_expansion.m.tpl
SCRATCH="_scratch_file"
OUTFILE_NAME=full_search_expansion

SEARCH_CASES=(
        "P=3;N=6;M=1;L=5;F=2"
        # "P=3;N=6;M=6;L=3;F=2;MS='[2,3]'"
        # "P=3;N=6;M=6;L=3;F=10;MS='[2,3]'"
        # "P=3;N=6;M=3;L=4;F=10;"
        # "P=3;N=6;M=2;L=5;F=10;MS='[1]'"
        # "P=3;N=6;M=3;L=5;F=10;MS='[1]'"
        # "P=3;N=8;M=8;L=2;F=2;MS='[4]'"
        # "P=3;N=8;M=8;L=2;F=4;MS='[4]'"
        # "P=3;N=8;M=2;L=4;F=2;"
        # "P=3;N=8;M=1;L=5;F=2;"
        # "P=3;N=8;M=1;L=5;F=10;"
        # "P=3;N=8;M=1;L=5;F=28;"
)

for SEARCH_CASE in ${SEARCH_CASES[@]}
do
        # Very sketchy but idc
        eval $SEARCH_CASE

        # No previous subfields were searched
        if [$MS -eq ""]
        then
                MS="[]"
        fi;

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
        sed "s/@MS@/${MS}/g" $OUTFILE > $SCRATCH
        cp $SCRATCH $OUTFILE

        screen -dm magma $OUTFILE
done