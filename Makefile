
# To use this makefile, do the following:
# 1. Update $(SRCS) to reflect the list of files you want to compile
# 2. Set $(OBJDIR) to the directory in which you want the intermediate files to be placed (and 
#    make sure the directory exists)
# 3. Change $(EXEC) to be the name you want for your executable

SRCS = bbr.c best_first_bbr.c bfs_bbr.c bin_packing.c hoffman.c io.c memory.c
CFLAGS = 
LDFLAGS = 
EXEC = salb

# You can leave this stuff alone for the most part; it sets the right C++ standard, tells the
# compiler to print output nicely, and prints some useful warning messages

CC = g++ 
STD = -std=c++0x
FORMAT = -fmessage-length=100 
WARNINGS = -Wempty-body -Wall -Wno-sign-compare
DEBUGFLAGS = -g -pg
OPTFLAGS = -O2
OBJDIR = obj
OBJS = $(addprefix $(OBJDIR)/,$(SRCS:.c=.o))
DOBJS = $(addprefix $(OBJDIR)/,$(SRCS:.c=.debug))
EXECD = $(EXEC)_d

.DEFAULT_GOAL := $(EXEC)
.PHONY: all clean debug

$(OBJDIR)/%.o : %.c $(OBJDIR)/%.d
	@echo; echo "Compiling $@ with $(CFLAGS) $(OPTFLAGS)"; echo "---"
	@$(CC) $(STD) $(WARNINGS) $(FORMAT) -o $@ $(CFLAGS) $(OPTFLAGS) -c $<

$(OBJDIR)/%.debug : %.c $(OBJDIR)/%.d
	@echo; echo "Compiling $@ with $(CFLAGS) $(DEBUGFLAGS)"; echo "---"
	@$(CC) $(STD) $(WARNINGS) $(FORMAT) -o $@ $(CFLAGS) $(DEBUGFLAGS) -c $<

# Use the -MM option for g++ or gcc to automatically determine dependency structure for $(SRCS).
# This will get stuck into a $(OBJDIR)/<sourcename>.d file, which the object files depend on.  Then,
# whenever any file in the dependency structure changes, we'll rebuild and remake.  Slick!
$(OBJDIR)/%.d : %.c 
	@$(SHELL) -ec "$(CC) $(STD) -MM $(CFLAGS) $< | \
		sed 's/\($*\)\.o[ :]*/$(OBJDIR)\/\1.o $(OBJDIR)\/\1.debug : /g' > $@; [ -s $@ ] || rm -f $@"

all: $(EXEC) $(EXECD)

debug: $(EXECD)

$(EXEC): $(OBJS)
	@echo; echo "Linking $(EXEC) with $(LDFLAGS)"
	@$(CC) $(STD) $(FORMAT) -o $(EXEC) $(OPTFLAGS) $(OBJS) $(LDFLAGS)
	@echo "Done."

$(EXECD): $(DOBJS)
	@echo; echo "Linking $(EXECD) with $(LDFLAGS)"
	@$(CC) $(STD) $(FORMAT) -o $(EXECD) $(DEBUGFLAGS) $(DOBJS) $(LDFLAGS)
	@echo "Done."

clean:
	-rm $(EXEC) $(EXECD) $(OBJDIR)/*.d $(OBJDIR)/*.debug $(OBJDIR)/*.o gmon.out;

include $(addprefix $(OBJDIR)/,$(SRCS:.c=.d))
