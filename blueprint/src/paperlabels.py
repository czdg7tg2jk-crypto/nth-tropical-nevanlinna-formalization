"""plasTeX support for labels attached to unnumbered theorem environments."""

from pathlib import Path
from plasTeX import Command
from plasTeX.PackageResource import PackageTemplateDir


def ProcessOptions(options, document):
    document.addPackageResource(PackageTemplateDir(path=Path(__file__).parent))


class paperlabel(Command):
    args = "label:str"

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.ownerDocument.context.label(
            self.attributes["label"], node=self.parentNode
        )
