PIDE_MCP=/Users/uqmuttin/git/isabelle/isabelle-pide-mcp
echo "switch git/isabelle/isabelle-pide-mcp to correct branch"
(cd $PIDE_MCP; git status)

echo "setting up PATH to correct Isabelle"
export PATH="/Applications/Isabelle2026.app/bin:$PATH"

isabelle components -u /Users/uqmuttin/git/isabelle/isabelle-pide-mcp
claude mcp add isabelle-pide-mcp -- $(which isabelle) pide_mcp -l HOL
