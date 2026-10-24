# Exact observable recurrence on connected quantum networks

Canonical replacement, 24 October 2026: main.tex + body.tex + references.tex, rendered as main.pdf.

The central new theorem extends exact continuous-time first-return exponents from local paths to every finite connected interaction graph, heterogeneous local dimensions, and support-contained connected hypergraphs. One conull Hamiltonian event works for every finite matrix observer. The complementary stationary law applies to every probability energy measure and recovers total point-spectrum mass from the upper support edge.

## Review materials

- claim-trace.md: each mathematical statement mapped to exact Lean declarations.
- proof-audit.md: source checks, transitive axioms, quantifiers, and proof-integrity boundaries.
- novelty-audit.md: current primary literature and the precise candidate contribution.
- hostile-review.md: adversarial review and remaining limitations.
- reference-audit.md: bibliographic verification.
- corpus-disposition.md: older manuscript results and competing routes.
- audit/declarations.txt, audit/check-axioms.sh, audit/axioms.log: reproducible dependency audit.
- audit/source-*.log, audit/pdf-build.log, audit/manifest.sha256: final source-check output, PDF build record, and artifact fingerprints.
- [Formalized theorem card](../../3-formalized/connected-network-all-observer-recurrence.md) and [completed research card](../../3-formalized/quantum-recurrence-strongest-form-2026-10.md).

The directory name is historical. This is a checked research manuscript, not a claim of independent peer review, priority certification, or journal acceptance. Human authorship metadata and the AI-assistance disclosure must be reviewed by the author before submission. Earlier AI systems were moved from the author line to a disclosure; no human author was removed or added.

## Historical files

The main-localization and main-observer-localization variants, prior-results-appendices.tex, new-appendices.tex, and localization/complexity audits and blueprints are earlier research. They are not included by the canonical manuscript and are not current claim ledgers. They remain available as research history; their references and cross-references are not maintained by this rewrite. Previous canonical text remains in Git history.

Pre-existing auxiliary files and earlier output directories were preserved. Replacement intermediate TeX and rendered-page files were kept outside this directory.

## Reproduce the PDF

From this directory, with Tectonic installed:

    mkdir -p /tmp/hgt-quantum-recurrence-paper
    tectonic --outdir /tmp/hgt-quantum-recurrence-paper --keep-logs main.tex

The source uses no external figures or bibliography database.

## Reproduce the Lean audit

From the repository's formal/ directory, check individual source modules with lake --old env lean. Do not compile either umbrella. Both new modules are imported by HTGeometry.lean.

Run audit/check-axioms.sh from any directory after required dependency oleans are present. It checks a temporary copy of current observer capstone source, then prints transitive axioms for the declaration list. It creates no capstone olean and rebuilds no existing artifact. Exact source-check results are recorded in proof-audit.md.
