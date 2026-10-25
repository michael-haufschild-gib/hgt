import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureEnclosures

/-!
# Certified constants and mesh endpoints

Each abbreviation pairs normalized integer bounds with an equality proof. Splitting powers and
endpoint recurrences into single steps keeps proof-producing reduction within the default limits.
-/

namespace RHTower.ThetaRationalQuadrature.Certificates

open Lean.Parser.Tactic.Conv in
macro "certify_first_atom" " => " s:convSeq : tactic =>
  `(tactic| (refine ⟨?_, ?_⟩; swap; conv_rhs => $s))

private theorem roundDown_eq_floor (x : ℚ) :
    roundDown x = (⌊x * 1000000000000⌋ : ℚ) / 1000000000000 := rfl

private theorem roundUp_eq_ceil (x : ℚ) :
    roundUp x = (⌈x * 1000000000000⌉ : ℚ) / 1000000000000 := by
  rw [roundUp, Rat.ceil_eq_neg_floor_neg]
  rfl

-- Numerical reflection avoids unfolding the rational field instance during scalar rounding.
macro "normalize_first_atom_seed" : conv => `(conv|
  norm_num [Enclosure.expLo, Enclosure.expHi, Enclosure.polyEval, Enclosure.polyPoint,
    Enclosure.point, Enclosure.add, Enclosure.neg, Enclosure.sub, Enclosure.mul,
    Enclosure.cornerLo, Enclosure.cornerHi, Enclosure.lower, Enclosure.upper,
    Enclosure.precision, Enclosure.down, Enclosure.up, roundDown_eq_floor, roundUp_eq_ceil,
    expNeg, expTwoTaylor, expTwoTaylorUpper, add, neg, sub, scale, mul, pow, C, X,
    List.ofFn_succ, List.foldr, min_def, max_def])

abbrev expLoData : {v // v = Enclosure.expLo} := by
  certify_first_atom => normalize_first_atom_seed

abbrev expHiData : {v // v = Enclosure.expHi} := by
  certify_first_atom => normalize_first_atom_seed

abbrev coeffData5 : {v // v = Enclosure.polyPoint (expNeg 5)} := by
  certify_first_atom => normalize_first_atom_seed

abbrev coeffData6 : {v // v = Enclosure.polyPoint (expNeg 6)} := by
  certify_first_atom => normalize_first_atom_seed

abbrev coeffData9 : {v // v = Enclosure.polyPoint (expNeg 9)} := by
  certify_first_atom => normalize_first_atom_seed

abbrev coeffData10 : {v // v = Enclosure.polyPoint (expNeg 10)} := by
  certify_first_atom => normalize_first_atom_seed

-- The command expands to ordinary equality certificates, one per power.
macro "first_atom_widths" : command => do
  let mut declarations := #[]
  for k in [:59] do
    let name := Lean.mkIdent (.mkSimple ("widthPower" ++ toString k))
    let n := Lean.Syntax.mkNumLit (toString k)
    let declaration ← if k == 0 then
      `(command| abbrev $name : {v // v = Enclosure.pow (Enclosure.point (1 / 64)) $n} := by
        certify_first_atom =>
          rw [Enclosure.pow]
          normalize_first_atom_seed)
    else do
      let prev := Lean.mkIdent (.mkSimple ("widthPower" ++ toString (k - 1)))
      `(command| abbrev $name : {v // v = Enclosure.pow (Enclosure.point (1 / 64)) $n} := by
        certify_first_atom =>
          rw [Enclosure.pow]
          simp only [← ($prev).property]
          dsimp only [$prev:ident]
          normalize_first_atom_seed)
    declarations := declarations.push declaration
  return ⟨Lean.mkNullNode declarations⟩

first_atom_widths

-- Both exponential directions and both rounded endpoints share the same mesh.
macro "first_atom_endpoints" : command => do
  let mut declarations := #[]
  for j in [:64] do
    let n := Lean.Syntax.mkNumLit (toString j)
    for side in ["Lo", "Hi"] do
      let name := Lean.mkIdent (.mkSimple ("power" ++ side ++ toString j))
      let exponential := Lean.mkIdent (if side == "Lo" then ``Enclosure.expLo else ``Enclosure.expHi)
      let data := Lean.mkIdent (.mkSimple ("exp" ++ side ++ "Data"))
      let declaration ← if j == 0 then
        `(command| abbrev $name : {v // v = Enclosure.pow $exponential $n} := by
          certify_first_atom =>
            rw [Enclosure.pow]
            normalize_first_atom_seed)
      else do
        let prev := Lean.mkIdent (.mkSimple ("power" ++ side ++ toString (j - 1)))
        `(command| abbrev $name : {v // v = Enclosure.pow $exponential $n} := by
          certify_first_atom =>
            rw [Enclosure.pow]
            simp only [← ($prev).property]
            dsimp only [$prev:ident]
            simp only [← ($data).property]
            dsimp only [$data:ident]
            normalize_first_atom_seed)
      declarations := declarations.push declaration
      let inc := Lean.mkIdent (.mkSimple ("increment" ++ side ++ toString j))
      let increment := Lean.mkIdent
        (if side == "Lo" then ``Enclosure.incrementLo else ``Enclosure.incrementHi)
      declarations := declarations.push (← `(command|
        abbrev $inc : {v // v = $increment $n} := by
          certify_first_atom =>
            rw [$increment:ident]
            simp only [← ($name).property]
            dsimp only [$name:ident]
            simp only [← ($data).property]
            dsimp only [$data:ident]
            normalize_first_atom_seed))
      let ep := Lean.mkIdent (.mkSimple ("endpoint" ++ side ++ toString j))
      let endpoint := Lean.mkIdent
        (if side == "Lo" then ``Enclosure.endpointLo else ``Enclosure.endpointHi)
      let declaration ← if j == 0 then
        `(command| abbrev $ep : {v // v = $endpoint $n} := by
          certify_first_atom =>
            rw [$endpoint:ident]
            normalize_first_atom_seed)
      else do
        let prev := Lean.mkIdent (.mkSimple ("endpoint" ++ side ++ toString (j - 1)))
        let opposite := if side == "Lo" then "Hi" else "Lo"
        let increment := Lean.mkIdent (.mkSimple ("increment" ++ opposite ++ toString (j - 1)))
        let coefficients := if side == "Lo" then Lean.mkIdent `coeffData10
          else Lean.mkIdent `coeffData9
        `(command| abbrev $ep : {v // v = $endpoint $n} := by
          certify_first_atom =>
            rw [$endpoint:ident]
            simp only [← ($prev).property]
            dsimp only [$prev:ident]
            simp only [← ($increment).property]
            dsimp only [$increment:ident]
            simp only [← ($coefficients).property]
            dsimp only [$coefficients:ident]
            normalize_first_atom_seed)
      declarations := declarations.push declaration
  return ⟨Lean.mkNullNode declarations⟩

first_atom_endpoints

end RHTower.ThetaRationalQuadrature.Certificates

set_option pp.proofs false in
#print RHTower.ThetaRationalQuadrature.Certificates.widthPower0
set_option pp.proofs false in
#print RHTower.ThetaRationalQuadrature.Certificates.widthPower1
set_option pp.proofs false in
#print RHTower.ThetaRationalQuadrature.Certificates.widthPower57
#print axioms RHTower.ThetaRationalQuadrature.Certificates.widthPower57
