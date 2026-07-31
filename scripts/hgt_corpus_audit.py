#!/usr/bin/env python3
"""Exhaustive source-level audit of HTGeometry and RHTower.

This complements the compiler-derived research-frontier graph.  It processes
every Lean source module even when a declaration is split across lines or the
module is not yet represented in a compiled cache.
"""

from __future__ import annotations

import argparse
import collections
import csv
import math
import re
from dataclasses import dataclass
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
FORMAL = ROOT / "formal" / "GaloisForLFunctions"
PIPELINE = ROOT / "docs" / "drafts" / "pipeline"
AREAS = ("HTGeometry", "RHTower")
STAGES = (
    "0-backlog",
    "1-in-progress",
    "2-fully-proven",
    "3-formalized",
    "4-publication-ready",
    "5-failed",
)

DECL_RE = re.compile(
    r"(?m)^[ \t]*"
    r"(?:(?:@\[[^\]]*\]|private|protected|noncomputable|local|scoped|unsafe)"
    r"[ \t\r\n]+)*"
    r"(theorem|lemma|def|structure|class|abbrev|inductive|instance)"
    r"[ \t\r\n]+([A-Za-z_][A-Za-z0-9_'.]*)"
)
IMPORT_RE = re.compile(
    r"(?m)^[ \t]*import[ \t]+GaloisForLFunctions\.(HTGeometry|RHTower)"
    r"\.([A-Za-z0-9_'.]+)"
)
TITLE_RE = re.compile(r"/-!\s*(?:\r?\n)?\s*#\s+([^\r\n]+)")
TOKEN_RE = re.compile(r"[A-Z]+(?=[A-Z][a-z]|$)|[A-Z]?[a-z]+|[0-9]+")
CARD_TOKEN_RE = re.compile(
    r"\b(?:GaloisForLFunctions\.)?(HTGeometry|RHTower)"
    r"(?:[/.])([A-Z][A-Za-z0-9_/.]*?)(?:\.lean)?\b"
    r"|`([A-Z][A-Za-z0-9_/]*)(?:\.lean)?`"
)
IDENTIFIER_RE = re.compile(r"[A-Za-z][A-Za-z0-9_'.]*")

SOURCE_SYMBOL_RE = re.compile(
    r"\b(?:riemannZeta|RHTower\.xi|xi|XiC|xiC|vonMangoldt|"
    r"mobius|mertens|primeArch|zetaUpperEndMero)\b",
    re.IGNORECASE,
)

DECLARATION_MECHANISMS: dict[str, tuple[str, ...]] = {
    "differential-algebra": (
        "Differential",
        "deriv",
        "Deriv",
        "jet",
        "Jet",
        "hypertrans",
        "Hypertrans",
        "algebraicIndependent",
        "DifferentiallyAlgebraic",
        "Kolchin",
    ),
    "gamma-special-functions": (
        "Gamma",
        "gamma",
        "digamma",
        "Digamma",
        "polygamma",
        "Polygamma",
        "Barnes",
        "theta",
        "Theta",
        "Hurwitz",
    ),
    "integral-transforms": (
        "Fourier",
        "Mellin",
        "Laplace",
        "Poisson",
        "Cauchy",
        "transform",
        "Transform",
        "convolution",
    ),
    "moment-positivity": (
        "moment",
        "Moment",
        "Hankel",
        "Toeplitz",
        "positiveDefinite",
        "PositiveDefinite",
        "nonneg",
        "Nonneg",
        "Gram",
        "Stieltjes",
        "Hausdorff",
        "Bernstein",
    ),
    "spectral-operator": (
        "spectrum",
        "Spectrum",
        "spectral",
        "Spectral",
        "Operator",
        "operator",
        "resolvent",
        "Resolvent",
        "eigen",
        "Eigen",
        "trace",
        "Trace",
        "Fredholm",
        "Krein",
    ),
    "measure-functional-analysis": (
        "Measure",
        "measure",
        "integral",
        "Integral",
        "Lp",
        "Hilbert",
        "Banach",
        "Schwartz",
        "weak",
        "Weak",
        "tight",
        "Tight",
        "functional",
        "Functional",
    ),
    "complex-analysis": (
        "Analytic",
        "analytic",
        "Holomorphic",
        "holomorphic",
        "Meromorphic",
        "meromorphic",
        "Entire",
        "entire",
        "Herglotz",
        "Nevanlinna",
        "Pick",
        "Hardy",
        "Blaschke",
    ),
    "arithmetic-dirichlet": (
        "Prime",
        "prime",
        "Dirichlet",
        "Euler",
        "Mobius",
        "mobius",
        "Mertens",
        "Valuation",
        "valuation",
        "vonMangoldt",
        "divisor",
        "Divisor",
    ),
    "algebraic-combinatorial": (
        "Polynomial",
        "MvPolynomial",
        "Matrix",
        "det",
        "Det",
        "rank",
        "Rank",
        "span",
        "Span",
        "Linear",
        "Finite",
        "finset",
        "Finset",
        "graph",
        "Graph",
        "matroid",
        "Matroid",
    ),
    "projective-geometric": (
        "Projective",
        "projective",
        "Horizon",
        "horizon",
        "Plucker",
        "Grassmann",
        "incidence",
        "Incidence",
        "coframe",
        "Coframe",
        "facet",
        "Facet",
    ),
    "asymptotic-order": (
        "Tendsto",
        "tendsto",
        "IsBigO",
        "IsLittleO",
        "Asymptotic",
        "asymptotic",
        "cofinal",
        "Cofinal",
        "eventually",
        "atTop",
        "summable",
        "Summable",
    ),
    "topology-compactness": (
        "Continuous",
        "continuous",
        "Compact",
        "compact",
        "closure",
        "Closure",
        "Dense",
        "dense",
        "Connected",
        "connected",
        "homeomorph",
        "Homeomorph",
    ),
    "dynamics-quantum": (
        "Dynamics",
        "dynamics",
        "orbit",
        "Orbit",
        "Quantum",
        "quantum",
        "KMS",
        "Thermal",
        "Clock",
        "clock",
        "Wigner",
        "Hamilton",
    ),
}

DECLARATION_SHAPES: dict[str, re.Pattern[str]] = {
    "iff-classification": re.compile(r"↔|<->"),
    "equality-identity": re.compile(r"(?<![<>!])=(?!=)|\brfl\b"),
    "inequality-order": re.compile(r"≤|≥|<|>|\bStrict(?:Anti|Mono)\b"),
    "existence-construction": re.compile(r"∃|Exists|Nonempty"),
    "universal-law": re.compile(r"∀|forall"),
    "negation-no-go": re.compile(r"¬|not_|_ne\b|≠|False"),
    "convergence-asymptotic": re.compile(
        r"Tendsto|IsBigO|IsLittleO|Summable|CauchySeq|atTop|eventually"
    ),
    "positivity-moment": re.compile(
        r"Positive|positive|Nonneg|nonneg|pos\b|Hankel|Moment|moment|Gram"
    ),
    "independence-transcendence": re.compile(
        r"[Ii]ndependent|[Tt]ranscend|DifferentiallyAlgebraic|DA\b"
    ),
    "regularity-analyticity": re.compile(
        r"Analytic|Holomorphic|Meromorphic|Entire|Continuous|Differentiable"
    ),
    "injectivity-equivalence": re.compile(
        r"Injective|Surjective|Bijective|Equiv|Embedding|Isometry"
    ),
    "rank-support-dimension": re.compile(
        r"rank|Rank|finrank|support|Support|dimension|Dimension|card|Card"
    ),
    "membership-span": re.compile(r"∈|∉|SetLike|span|Span|range|Range"),
}

# These labels describe what a declaration can supply, not merely its subject.
# `declaration_parts` separates binder hypotheses from the result before these
# patterns are applied, so an assumed positivity hypothesis is not counted as a
# produced positivity theorem.
DECLARATION_CAPABILITIES: dict[str, re.Pattern[str]] = {
    "sign-orientation": re.compile(
        r"\b(?:StrictAnti|StrictMono|Monotone|Antitone|Accretive|Dissipative)\b"
        r"|(?:_pos|_neg|_nonneg|_nonpos|_sign|Orientation|orientation)"
        r"|(?:0\s*[<≤]\s*|[<≤]\s*0\b)"
    ),
    "positive-kernel-form": re.compile(
        r"PositiveDefinite|PosSemidef|posSemidef|Nonnegative|"
        r"Hankel|Toeplitz|Gram|Loewner|Pick|Herglotz|Nevanlinna"
    ),
    "quantitative-bound": re.compile(
        r"\b(?:IsBigO|IsLittleO|Bounded|Semibounded|Summable|"
        r"PolynomiallyModerate|Subpower|Decay|Coercive)\b"
        r"|(?:_le|_lt|_ge|_gt|Bound|bound|estimate|Estimate)"
    ),
    "limit-compactness": re.compile(
        r"Tendsto|CauchySeq|Compact|Precompact|Tight|closure|Closure|"
        r"ClusterPt|Cofinal|WeakConvergence|Converges"
    ),
    "analytic-continuation": re.compile(
        r"Analytic|Holomorphic|Meromorphic|Entire|Continuation|"
        r"poleFree|PoleFree|zeroFree|ZeroFree"
    ),
    "zero-location-exclusion": re.compile(
        r"\bzero(?:s|Set|Free)?\b|\bZero(?:s|Set|Free)?\b|"
        r"vanish|Vanish|root|Root|divisor|Divisor"
    ),
    "spectral-reality": re.compile(
        r"Spectrum|spectrum|Spectral|spectral|SelfAdjoint|selfAdjoint|"
        r"Unitary|unitary|Eigen|eigen|Resolvent|resolvent|Krein|Fredholm"
    ),
    "measure-representation": re.compile(
        r"\bMeasure\b|RepresentingMeasure|momentFunctional|"
        r"IntegralRepresentation|Bochner|RieszRepresentation|Stieltjes"
    ),
    "factorization-decomposition": re.compile(
        r"Factorization|factorization|Decomposition|decomposition|"
        r"_mul_eq|_eq_mul|prod|Prod|convolution|Convolution|"
        r"DirectSum|Orthogonal"
    ),
    "rigidity-classification": re.compile(
        r"\b(?:Unique|unique|Injective|Surjective|Bijective|Equiv|Embedding)\b"
        r"|(?:_iff|classification|Classification|Rigidity|rigidity|"
        r"determines|Determines)"
    ),
    "rank-dimension-support": re.compile(
        r"\b(?:rank|Rank|finrank|dimension|Dimension|support|Support|"
        r"FiniteRank|corank|Corank)\b"
    ),
    "recurrence-almost-periodic": re.compile(
        r"Bohr|AlmostPeriodic|almostPeriodic|Recurrence|recurrence|"
        r"relativelyDense|ReturnTime|Orbit"
    ),
    "reflection-phase": re.compile(
        r"Reflection|reflection|Reflected|reflected|FunctionalEquation|"
        r"phase|Phase|involution|Involution|conj|Conj"
    ),
    "differential-transcendence": re.compile(
        r"Hypertranscend|hypertranscend|DifferentiallyAlgebraic|"
        r"AlgebraicIndependent|DifferentialIndependent|Kolchin"
    ),
    "arithmetic-source": re.compile(
        r"Prime|prime|Euler|Dirichlet|vonMangoldt|Mobius|mobius|"
        r"Mertens|Valuation|valuation|divisor|Divisor"
    ),
}

MATCH_STOPWORDS = {
    "a",
    "an",
    "and",
    "at",
    "by",
    "class",
    "def",
    "exists",
    "false",
    "fin",
    "for",
    "forall",
    "fun",
    "have",
    "iff",
    "if",
    "in",
    "instance",
    "is",
    "lemma",
    "let",
    "nat",
    "of",
    "on",
    "or",
    "prop",
    "real",
    "riemann",
    "hypothesis",
    "riemannhypothesis",
    "set",
    "structure",
    "the",
    "theorem",
    "then",
    "to",
    "true",
    "type",
    "with",
}
RH_RE = re.compile(r"\bRiemannHypothesis\b")
RH_IFF_RE = re.compile(
    r"(?:↔|<->)[^:\n]*\bRiemannHypothesis\b"
    r"|\bRiemannHypothesis\b[^:\n]*(?:↔|<->)"
)
NO_GO_RE = re.compile(
    r"(?:NoGo|Nogo|Obstruction|Blindness|Impossible|Insufficient|"
    r"Nonclos|Fracture|Barrier|Counterexample|Failure|Cannot|Collapse)"
)
OPEN_RE = re.compile(
    r"\b(?:open (?:core|wall|premise|problem|input)|remains? (?:open|unproved)|"
    r"conjectur|missing (?:theorem|input|bound|estimate|construction))\b",
    re.IGNORECASE,
)

FAMILIES: dict[str, dict[str, tuple[str, ...]]] = {
    "HTGeometry": {
        "differential-hypertranscendence": (
            "Differential",
            "Hypertrans",
            "Kolchin",
            "Deriv",
            "Jet",
            "Matroid",
            "DA",
        ),
        "gamma-theta-special-functions": (
            "Gamma",
            "Digamma",
            "Polygamma",
            "Elliptic",
            "Theta",
            "Sine",
            "Factorial",
            "Barnes",
        ),
        "projective-horizon-geometry": (
            "Projective",
            "Horizon",
            "Observer",
            "Facet",
            "Coframe",
            "Gauge",
            "Plucker",
        ),
        "algebraic-combinatorial-incidence": (
            "Algebra",
            "Arithmetic",
            "Combinatorial",
            "Determinant",
            "Field",
            "Polynomial",
            "Mv",
            "Stanley",
            "Reisner",
            "Hochster",
            "Incidence",
            "Constraint",
            "Boolean",
            "Face",
            "Graph",
            "Finite",
            "Linear",
            "Module",
            "Rank",
            "Ring",
        ),
        "analytic-boundary-function-spaces": (
            "Analytic",
            "Meromorphic",
            "Hardy",
            "Schwartz",
            "Nevanlinna",
            "Herglotz",
            "Cauchy",
            "Boundary",
            "UpperEnd",
            "Runge",
            "Bessel",
            "Complex",
            "Entire",
            "Fourier",
            "Harmonic",
            "Holomorphic",
            "Kernel",
            "Poisson",
            "Real",
            "Series",
            "Smooth",
        ),
        "moment-operator-spectral": (
            "Moment",
            "Hankel",
            "Hilbert",
            "Spectral",
            "Operator",
            "Matrix",
            "Krein",
            "Szego",
            "Wigner",
            "Measure",
            "Gram",
            "Positive",
            "Recurrence",
            "Trace",
        ),
        "prime-dirichlet-source": (
            "Prime",
            "Dirichlet",
            "Euler",
            "Mobius",
            "Valuation",
            "Bohr",
        ),
        "quantum-clock-observer": (
            "Quantum",
            "Clock",
            "Thermal",
            "KMS",
            "Fisher",
            "Witten",
            "Event",
        ),
    },
    "RHTower": {
        "xi-zeta-foundation": (
            "Xi",
            "Zeta",
            "Riemann",
            "Zero",
            "Divisor",
            "FE",
            "Completed",
            "Critical",
            "Reflection",
            "Seam",
        ),
        "prime-euler-mobius-arithmetic": (
            "Prime",
            "Euler",
            "Mobius",
            "Mangoldt",
            "Dirichlet",
            "Mertens",
            "Perron",
            "Landau",
            "Squarefree",
            "Bourgain",
            "Selberg",
            "AFE",
            "Arithmetic",
            "Coefficient",
            "Log",
            "Valuation",
        ),
        "gamma-theta-archimedean": (
            "Gamma",
            "Theta",
            "Hedenmalm",
            "Hurwitz",
            "Heat",
            "Gaussian",
            "Mellin",
            "Archimedean",
        ),
        "explicit-formula-positivity-moments": (
            "Weil",
            "Guinand",
            "Li",
            "Hankel",
            "Moment",
            "Bernstein",
            "Cauchy",
            "Stieltjes",
            "Herglotz",
            "Pick",
            "Trace",
            "Positiv",
            "Gram",
            "Kernel",
            "Matrix",
            "Measure",
        ),
        "sonin-fourier-copoisson": (
            "Sonin",
            "Fourier",
            "CoPoisson",
            "Poisson",
            "Burnol",
            "Aperture",
        ),
        "operator-spectral-ccm-suzuki": (
            "Operator",
            "Spectral",
            "Spectrum",
            "Resolvent",
            "SelfAdjoint",
            "Prolate",
            "CCM",
            "Suzuki",
            "Slepian",
            "Hermite",
            "Krein",
            "Finite",
            "Fredholm",
            "Hilbert",
            "Rank",
        ),
        "deninger-arithmetic-geometry": (
            "Deninger",
            "Arakelov",
            "Kummer",
            "Hodge",
            "Milnor",
            "Tate",
            "Cohom",
            "Witt",
        ),
        "dynamics-projective-quantum": (
            "Projective",
            "Bottcher",
            "Julia",
            "Dynamics",
            "Quantum",
            "Born",
            "KMS",
            "Fisher",
            "Thermal",
            "FieldOne",
        ),
        "growth-approximation-density": (
            "Analytic",
            "Bound",
            "Boundary",
            "Complex",
            "Decay",
            "Entire",
            "Asymptotic",
            "Density",
            "Hardy",
            "Holomorphic",
            "Meromorphic",
            "Approximation",
            "LargeSieve",
            "Subpower",
            "Window",
            "Cofinal",
        ),
    },
}


@dataclass(frozen=True)
class Declaration:
    kind: str
    name: str
    line: int
    header: str


@dataclass
class ModuleRow:
    area: str
    module: str
    relpath: str
    title: str
    imports: int
    direct_umbrella: bool
    umbrella_reachable: bool
    declaration_counts: collections.Counter[str]
    primary_family: str
    families: tuple[str, ...]
    roles: tuple[str, ...]
    stages: tuple[str, ...]
    declarations: tuple[Declaration, ...]


def strip_comments_and_strings(source: str) -> str:
    """Replace comments and strings with spaces while preserving newlines."""
    out: list[str] = []
    index = 0
    block_depth = 0
    line_comment = False
    string = False
    escaped = False
    while index < len(source):
        char = source[index]
        next_char = source[index + 1] if index + 1 < len(source) else ""
        if line_comment:
            if char == "\n":
                line_comment = False
                out.append("\n")
            else:
                out.append(" ")
            index += 1
            continue
        if block_depth:
            if char == "/" and next_char == "-":
                block_depth += 1
                out.extend((" ", " "))
                index += 2
            elif char == "-" and next_char == "/":
                block_depth -= 1
                out.extend((" ", " "))
                index += 2
            else:
                out.append("\n" if char == "\n" else " ")
                index += 1
            continue
        if string:
            if char == "\n":
                out.append("\n")
            else:
                out.append(" ")
            if escaped:
                escaped = False
            elif char == "\\":
                escaped = True
            elif char == '"':
                string = False
            index += 1
            continue
        if char == "-" and next_char == "-":
            line_comment = True
            out.extend((" ", " "))
            index += 2
        elif char == "/" and next_char == "-":
            block_depth = 1
            out.extend((" ", " "))
            index += 2
        elif char == '"':
            string = True
            out.append(" ")
            index += 1
        else:
            out.append(char)
            index += 1
    return "".join(out)


def declaration_header(segment: str) -> str:
    stops = [
        position
        for token in (":=", "\nby\n", "\nby ", "\nwhere\n", "\nwhere ")
        if (position := segment.find(token)) >= 0
    ]
    if stops:
        segment = segment[: min(stops)]
    return re.sub(r"\s+", " ", segment).strip()


def declaration_parts(header: str) -> tuple[str, str]:
    """Split a declaration header into binder/premise text and result text.

    Lean binder type colons occur inside `()`, `{}`, or `[]`; the first
    top-level colon after the declaration name introduces the result.
    """
    match = re.match(
        r"(?:(?:@\[[^\]]*\]|private|protected|noncomputable|local|scoped|unsafe)\s+)*"
        r"(?:theorem|lemma|def|structure|class|abbrev|inductive|instance)\s+"
        r"[A-Za-z_][A-Za-z0-9_'.]*",
        header,
    )
    if not match:
        return header, ""
    depths = {"(": 0, "{": 0, "[": 0}
    closing = {")": "(", "}": "{", "]": "["}
    for index in range(match.end(), len(header)):
        char = header[index]
        if char in depths:
            depths[char] += 1
        elif char in closing:
            opener = closing[char]
            depths[opener] = max(0, depths[opener] - 1)
        elif char == ":" and not any(depths.values()):
            return header[match.end() : index].strip(), header[index + 1 :].strip()
    return header[match.end() :].strip(), ""


def declarations(source: str) -> list[Declaration]:
    code = strip_comments_and_strings(source)
    matches = list(DECL_RE.finditer(code))
    result: list[Declaration] = []
    for index, match in enumerate(matches):
        end = matches[index + 1].start() if index + 1 < len(matches) else len(code)
        result.append(
            Declaration(
                kind=match.group(1),
                name=match.group(2),
                line=code.count("\n", 0, match.start()) + 1,
                header=declaration_header(code[match.start() : end]),
            )
        )
    return result


def declaration_mechanisms(header: str) -> tuple[str, ...]:
    """Overlapping mathematical mechanisms visible in one exact declaration header."""
    return tuple(
        mechanism
        for mechanism, needles in DECLARATION_MECHANISMS.items()
        if any(needle in header for needle in needles)
    )


def declaration_shapes(header: str) -> tuple[str, ...]:
    """Overlapping logical/conclusion shapes visible in one exact declaration header."""
    shapes = tuple(
        shape for shape, pattern in DECLARATION_SHAPES.items() if pattern.search(header)
    )
    return shapes or ("other",)


def declaration_capabilities(text: str) -> tuple[str, ...]:
    """Overlapping mathematical capabilities visible in exact Lean text."""
    return tuple(
        capability
        for capability, pattern in DECLARATION_CAPABILITIES.items()
        if pattern.search(text)
    )


def match_tokens(text: str) -> set[str]:
    """Normalize Lean identifiers for theorem-interface matching."""
    tokens: set[str] = set()
    for identifier in IDENTIFIER_RE.findall(text):
        for component in re.split(r"[._']", identifier):
            for token in TOKEN_RE.findall(component):
                lowered = token.lower()
                if len(lowered) > 1 and lowered not in MATCH_STOPWORDS:
                    tokens.add(lowered)
    return tokens


def title_of(source: str, fallback: str) -> str:
    match = TITLE_RE.search(source)
    if not match:
        return fallback
    return re.sub(r"\s+", " ", match.group(1)).strip()


def module_tokens(module: str, title: str, declaration_names: list[str]) -> set[str]:
    text = " ".join((module, title, *declaration_names))
    return set(TOKEN_RE.findall(text))


def family_scores(area: str, tokens: set[str]) -> dict[str, int]:
    lower = {token.lower() for token in tokens}
    return {
        family: sum(keyword.lower() in lower for keyword in keywords)
        for family, keywords in FAMILIES[area].items()
    }


def module_roles(
    module: str, title: str, source: str, decls: list[Declaration]
) -> tuple[str, ...]:
    headers = "\n".join(declaration.header for declaration in decls)
    theorem_headers = [
        declaration.header
        for declaration in decls
        if declaration.kind in ("theorem", "lemma")
    ]
    roles: set[str] = set()
    if SOURCE_SYMBOL_RE.search(headers):
        roles.add("literal-source")
    if any(RH_IFF_RE.search(header) for header in theorem_headers):
        roles.add("rh-equivalence")
    if any(RH_RE.search(header) for header in theorem_headers):
        roles.add("rh-facing")
        if any(
            re.search(r":\s*(?:¬\s*)?RiemannHypothesis\s*$", header)
            for header in theorem_headers
        ):
            roles.add("rh-conclusion")
        if any(
            re.search(r"\([^)]*:\s*RiemannHypothesis[^)]*\)", header)
            for header in theorem_headers
        ):
            roles.add("rh-premise")
    if NO_GO_RE.search(module) or NO_GO_RE.search(title):
        roles.add("no-go-or-obstruction")
    if OPEN_RE.search(source):
        roles.add("declared-open-wall")
    if not roles:
        roles.add("general-infrastructure")
    return tuple(sorted(roles))


def all_module_paths() -> dict[tuple[str, str], Path]:
    result: dict[tuple[str, str], Path] = {}
    for area in AREAS:
        for path in sorted((FORMAL / area).rglob("*.lean")):
            suffix = path.relative_to(FORMAL / area).with_suffix("").as_posix()
            result[(area, suffix)] = path
    return result


def pipeline_references(
    modules: dict[tuple[str, str], Path],
) -> dict[tuple[str, str], set[str]]:
    references: dict[tuple[str, str], set[str]] = collections.defaultdict(set)
    by_basename: dict[str, list[tuple[str, str]]] = collections.defaultdict(list)
    for key in modules:
        by_basename[key[1].split("/")[-1]].append(key)

    for stage in STAGES:
        stage_root = PIPELINE / stage
        if not stage_root.exists():
            continue
        for card in stage_root.rglob("*.md"):
            text = card.read_text(encoding="utf-8", errors="replace")
            for match in CARD_TOKEN_RE.finditer(text):
                if match.group(1):
                    area = match.group(1)
                    suffix = match.group(2).replace(".", "/")
                    key = (area, suffix)
                    if key in modules:
                        references[key].add(stage)
                        continue
                    candidates = by_basename.get(suffix.split("/")[-1], [])
                    if len(candidates) == 1:
                        references[candidates[0]].add(stage)
                elif match.group(3):
                    token = match.group(3)
                    candidates = by_basename.get(token.split("/")[-1], [])
                    if len(candidates) == 1:
                        references[candidates[0]].add(stage)
    return references


def import_graph(
    modules: dict[tuple[str, str], Path],
) -> tuple[
    dict[tuple[str, str], set[tuple[str, str]]],
    dict[str, set[tuple[str, str]]],
    dict[str, set[tuple[str, str]]],
]:
    graph: dict[tuple[str, str], set[tuple[str, str]]] = {}
    for key, path in modules.items():
        source = strip_comments_and_strings(
            path.read_text(encoding="utf-8", errors="replace")
        )
        graph[key] = {
            (area, suffix.replace(".", "/"))
            for area, suffix in IMPORT_RE.findall(source)
            if (area, suffix.replace(".", "/")) in modules
        }

    direct: dict[str, set[tuple[str, str]]] = {}
    reachable: dict[str, set[tuple[str, str]]] = {}
    for area in AREAS:
        umbrella = FORMAL / f"{area}.lean"
        source = strip_comments_and_strings(
            umbrella.read_text(encoding="utf-8", errors="replace")
        )
        seeds = {
            (import_area, suffix.replace(".", "/"))
            for import_area, suffix in IMPORT_RE.findall(source)
            if (import_area, suffix.replace(".", "/")) in modules
        }
        direct[area] = seeds
        seen = set(seeds)
        stack = list(seeds)
        while stack:
            current = stack.pop()
            for dependency in graph.get(current, set()):
                if dependency not in seen:
                    seen.add(dependency)
                    stack.append(dependency)
        reachable[area] = seen
    return graph, direct, reachable


def audit_rows() -> list[ModuleRow]:
    modules = all_module_paths()
    stage_refs = pipeline_references(modules)
    graph, direct, reachable = import_graph(modules)
    rows: list[ModuleRow] = []
    for (area, suffix), path in sorted(modules.items()):
        source = path.read_text(encoding="utf-8", errors="replace")
        decls = declarations(source)
        counts = collections.Counter(declaration.kind for declaration in decls)
        title = title_of(source, suffix.split("/")[-1])
        tokens = module_tokens(suffix, title, [declaration.name for declaration in decls])
        scores = family_scores(area, tokens)
        ranked = sorted(scores, key=lambda family: (-scores[family], family))
        positive = tuple(family for family in ranked if scores[family] > 0)
        primary = (
            ranked[0]
            if scores[ranked[0]] > 0
            else "cross-cutting-foundational"
        )
        imports = len(graph[(area, suffix)])
        rows.append(
            ModuleRow(
                area=area,
                module=suffix,
                relpath=path.relative_to(ROOT).as_posix(),
                title=title,
                imports=imports,
                direct_umbrella=(area, suffix) in direct[area],
                umbrella_reachable=(area, suffix) in reachable[area],
                declaration_counts=counts,
                primary_family=primary,
                families=positive,
                roles=module_roles(suffix, title, source, decls),
                stages=tuple(sorted(stage_refs.get((area, suffix), set()))),
                declarations=tuple(decls),
            )
        )
    return rows


def write_manifest(rows: list[ModuleRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            (
                "area",
                "module",
                "relpath",
                "title",
                "imports",
                "direct_umbrella",
                "umbrella_reachable",
                "declarations",
                "theorems_lemmas",
                "definitions",
                "primary_family",
                "families",
                "roles",
                "pipeline_stages",
            )
        )
        for row in rows:
            writer.writerow(
                (
                    row.area,
                    row.module,
                    row.relpath,
                    row.title,
                    row.imports,
                    "yes" if row.direct_umbrella else "no",
                    "yes" if row.umbrella_reachable else "no",
                    sum(row.declaration_counts.values()),
                    row.declaration_counts["theorem"] + row.declaration_counts["lemma"],
                    row.declaration_counts["def"] + row.declaration_counts["abbrev"],
                    row.primary_family,
                    ",".join(row.families),
                    ",".join(row.roles),
                    ",".join(row.stages),
                )
            )


def rh_declaration_roles(header: str) -> tuple[str, ...]:
    roles: list[str] = []
    if RH_IFF_RE.search(header):
        roles.append("rh-equivalence")
    if re.search(r":\s*RiemannHypothesis\s*$", header):
        roles.append("rh-conclusion")
    if re.search(r":\s*¬\s*RiemannHypothesis\s*$", header):
        roles.append("anti-rh-conclusion")
    if re.search(r"\([^)]*:\s*RiemannHypothesis[^)]*\)", header):
        roles.append("rh-premise")
    if re.search(r"\([^)]*:\s*¬\s*RiemannHypothesis[^)]*\)", header):
        roles.append("anti-rh-premise")
    if not roles:
        roles.append("rh-embedded")
    if SOURCE_SYMBOL_RE.search(header):
        roles.append("literal-source-in-statement")
    else:
        roles.append("named-interface-only")
    return tuple(roles)


def write_rh_declarations(rows: list[ModuleRow], path: Path) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            (
                "module",
                "declaration",
                "line",
                "roles",
                "pipeline_stages",
                "statement",
            )
        )
        for row in rows:
            if row.area != "RHTower":
                continue
            for declaration in row.declarations:
                if declaration.kind not in ("theorem", "lemma"):
                    continue
                if not RH_RE.search(declaration.header):
                    continue
                writer.writerow(
                    (
                        row.module,
                        declaration.name,
                        declaration.line,
                        ",".join(rh_declaration_roles(declaration.header)),
                        ",".join(row.stages),
                        declaration.header,
                    )
                )


def write_declarations(rows: list[ModuleRow], path: Path) -> None:
    """Write every parsed declaration without using import or prior-use relevance."""
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            (
                "area",
                "module",
                "declaration",
                "kind",
                "line",
                "mechanisms",
                "shapes",
                "premise_capabilities",
                "conclusion_capabilities",
                "statement",
            )
        )
        for row in rows:
            for declaration in row.declarations:
                premises, conclusion = declaration_parts(declaration.header)
                writer.writerow(
                    (
                        row.area,
                        row.module,
                        declaration.name,
                        declaration.kind,
                        declaration.line,
                        ",".join(
                            declaration_mechanisms(
                                f"{row.module} {row.title} {declaration.header}"
                            )
                        ),
                        ",".join(declaration_shapes(declaration.header)),
                        ",".join(declaration_capabilities(premises)),
                        ",".join(declaration_capabilities(conclusion)),
                        declaration.header,
                    )
                )


def write_crossmatches(rows: list[ModuleRow], path: Path, limit: int) -> None:
    """Match every RH-equivalent interface against every HT theorem producer.

    Selection uses exact conclusion capability and normalized type vocabulary,
    never import reachability or whether RHTower already cites the HT module.
    Output is a search surface; exact hypothesis compatibility still requires
    mathematical audit.
    """
    ht_entries: list[
        tuple[ModuleRow, Declaration, set[str], set[str], set[str]]
    ] = []
    document_frequency: collections.Counter[str] = collections.Counter()
    for row in rows:
        if row.area != "HTGeometry":
            continue
        for declaration in row.declarations:
            if declaration.kind not in ("theorem", "lemma"):
                continue
            premises, conclusion = declaration_parts(declaration.header)
            premise_capabilities = set(declaration_capabilities(premises))
            conclusion_capabilities = set(declaration_capabilities(conclusion))
            produced = conclusion_capabilities - premise_capabilities
            if not produced:
                continue
            tokens = match_tokens(
                f"{row.module} {row.title} {declaration.name} {conclusion}"
            )
            document_frequency.update(tokens)
            ht_entries.append((row, declaration, produced, conclusion_capabilities, tokens))

    walls: list[tuple[ModuleRow, Declaration, set[str], set[str]]] = []
    for row in rows:
        if row.area != "RHTower":
            continue
        for declaration in row.declarations:
            if declaration.kind not in ("theorem", "lemma"):
                continue
            if not RH_IFF_RE.search(declaration.header):
                continue
            _, conclusion = declaration_parts(declaration.header)
            capabilities = set(declaration_capabilities(conclusion))
            tokens = match_tokens(
                f"{row.module} {row.title} {declaration.name} {conclusion}"
            )
            walls.append((row, declaration, capabilities, tokens))

    corpus_size = max(1, len(ht_entries))
    path.parent.mkdir(parents=True, exist_ok=True)
    with path.open("w", encoding="utf-8", newline="") as handle:
        writer = csv.writer(handle, delimiter="\t", lineterminator="\n")
        writer.writerow(
            (
                "wall_module",
                "wall_declaration",
                "wall_line",
                "wall_capabilities",
                "rank",
                "score",
                "shared_capabilities",
                "shared_tokens",
                "ht_module",
                "ht_declaration",
                "ht_line",
                "ht_produced_capabilities",
                "ht_statement",
                "wall_statement",
            )
        )
        for wall_row, wall_declaration, wall_capabilities, wall_tokens in walls:
            scored: list[
                tuple[
                    float,
                    tuple[str, ...],
                    tuple[str, ...],
                    ModuleRow,
                    Declaration,
                    set[str],
                ]
            ] = []
            for (
                ht_row,
                ht_declaration,
                produced,
                _conclusion_capabilities,
                ht_tokens,
            ) in ht_entries:
                shared_capabilities = tuple(sorted(wall_capabilities & produced))
                if not shared_capabilities:
                    continue
                shared_tokens = tuple(sorted(wall_tokens & ht_tokens))
                token_score = sum(
                    math.log((corpus_size + 1) / (document_frequency[token] + 1))
                    for token in shared_tokens
                )
                score = 4.0 * len(shared_capabilities) + token_score
                scored.append(
                    (
                        score,
                        shared_capabilities,
                        shared_tokens,
                        ht_row,
                        ht_declaration,
                        produced,
                    )
                )
            scored.sort(
                key=lambda item: (
                    -item[0],
                    item[3].module,
                    item[4].name,
                )
            )
            for rank, (
                score,
                shared_capabilities,
                shared_tokens,
                ht_row,
                ht_declaration,
                produced,
            ) in enumerate(scored[:limit], start=1):
                writer.writerow(
                    (
                        wall_row.module,
                        wall_declaration.name,
                        wall_declaration.line,
                        ",".join(sorted(wall_capabilities)),
                        rank,
                        f"{score:.6f}",
                        ",".join(shared_capabilities),
                        ",".join(shared_tokens),
                        ht_row.module,
                        ht_declaration.name,
                        ht_declaration.line,
                        ",".join(sorted(produced)),
                        ht_declaration.header,
                        wall_declaration.header,
                    )
                )


def summary(rows: list[ModuleRow]) -> str:
    lines = ["# Whole formal corpus audit summary", ""]
    for area in AREAS:
        area_rows = [row for row in rows if row.area == area]
        declarations_total = sum(
            sum(row.declaration_counts.values()) for row in area_rows
        )
        lines.extend(
            (
                f"## {area}",
                "",
                f"- modules: {len(area_rows)}",
                f"- directly parsed declarations: {declarations_total}",
                f"- cross-cutting foundational primary family: "
                f"{sum(row.primary_family == 'cross-cutting-foundational' for row in area_rows)}"
                "",
                f"- umbrella reachable: "
                f"{sum(row.umbrella_reachable for row in area_rows)}",
                f"- umbrella unreachable: "
                f"{sum(not row.umbrella_reachable for row in area_rows)}",
                "",
                "### Primary mechanism families",
                "",
            )
        )
        family_counts = collections.Counter(row.primary_family for row in area_rows)
        for family, count in family_counts.most_common():
            lines.append(f"- {family}: {count}")
        lines.extend(("", "### Module roles", ""))
        role_counts = collections.Counter(
            role for row in area_rows for role in row.roles
        )
        for role, count in role_counts.most_common():
            lines.append(f"- {role}: {count}")
        lines.extend(("", "### Pipeline references", ""))
        for stage in STAGES:
            lines.append(
                f"- {stage}: {sum(stage in row.stages for row in area_rows)}"
            )
        lines.append(
            f"- no detected pipeline reference: "
            f"{sum(not row.stages for row in area_rows)}"
        )
        lines.append("")
    return "\n".join(lines).rstrip() + "\n"


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--manifest", type=Path)
    parser.add_argument("--declarations", type=Path)
    parser.add_argument("--rh-declarations", type=Path)
    parser.add_argument("--crossmatches", type=Path)
    parser.add_argument("--crossmatch-limit", type=int, default=12)
    parser.add_argument("--summary", type=Path)
    args = parser.parse_args()
    rows = audit_rows()
    if args.manifest:
        write_manifest(rows, args.manifest)
    if args.declarations:
        write_declarations(rows, args.declarations)
    if args.rh_declarations:
        write_rh_declarations(rows, args.rh_declarations)
    if args.crossmatches:
        write_crossmatches(rows, args.crossmatches, args.crossmatch_limit)
    rendered = summary(rows)
    if args.summary:
        args.summary.parent.mkdir(parents=True, exist_ok=True)
        args.summary.write_text(rendered, encoding="utf-8")
    else:
        print(rendered, end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
