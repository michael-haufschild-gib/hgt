import GaloisForLFunctions.RHTower.PrimeArchThetaFirstAtomQuadratureSeeds

/-!
# Equality certificates for a quadrature cell

Horner composition, coefficient multiplication, and integration are normalized separately.
Every normalized value retains an equality proof to the enclosure it represents.
-/

namespace RHTower.ThetaRationalQuadrature.Certificates

macro "first_atom_cell " j:num : command => do
  let mut declarations := #[]
  let index := toString j.getNat
  for side in ["Lo", "Hi"] do
    let power := Lean.mkIdent (.mkSimple ("power" ++ side ++ index))
    let source := Lean.mkIdent (.mkSimple ("source" ++ side ++ index))
    let sourceFn := Lean.mkIdent
      (if side == "Lo" then ``Enclosure.sourceLo else ``Enclosure.sourceHi)
    declarations := declarations.push (← `(command|
      abbrev $source : {v // v = $sourceFn $j} := by
        certify_first_atom =>
          rw [$sourceFn:ident]
          simp only [← ($power).property]
          dsimp only [$power:ident]
          cbv))
    let delta := Lean.mkIdent (.mkSimple ("delta" ++ side ++ index))
    let deltaFn := Lean.mkIdent
      (if side == "Lo" then ``Enclosure.deltaLo else ``Enclosure.deltaHi)
    declarations := declarations.push (← `(command|
      abbrev $delta : {v // v = $deltaFn $j} := by
        certify_first_atom =>
          rw [$deltaFn:ident]
          simp only [← ($power).property]
          dsimp only [$power:ident]
          cbv))
  for side in ["Lo", "Hi"] do
    let count := if side == "Lo" then 6 else 5
    let coefficients := Lean.mkIdent
      (if side == "Lo" then ``coeffData6 else ``coeffData5)
    let opposite := if side == "Lo" then "Hi" else "Lo"
    let delta := Lean.mkIdent (.mkSimple ("delta" ++ opposite ++ index))
    let deltaFn := Lean.mkIdent
      (if side == "Lo" then ``Enclosure.deltaHi else ``Enclosure.deltaLo)
    for offset in [:count + 1] do
      let k := count - offset
      let n := Lean.Syntax.mkNumLit (toString k)
      let name := Lean.mkIdent (.mkSimple ("local" ++ side ++ index ++ "Stage" ++ toString k))
      let declaration ← if k == count then
        `(command| abbrev $name :
            {v // v = Enclosure.polyComp (($coefficients).val.drop $n) ($deltaFn $j)} := by
          certify_first_atom =>
            change ([] : List Enclosure.Bounds)
            cbv)
      else do
        let next := Lean.Syntax.mkNumLit (toString (k + 1))
        let prev := Lean.mkIdent
          (.mkSimple ("local" ++ side ++ index ++ "Stage" ++ toString (k + 1)))
        `(command| abbrev $name :
            {v // v = Enclosure.polyComp (($coefficients).val.drop $n) ($deltaFn $j)} := by
          certify_first_atom =>
            change Enclosure.polyAdd [(($coefficients).val[$n]?).getD (Enclosure.point 0)]
              (Enclosure.polyMul ($deltaFn $j)
                (Enclosure.polyComp (($coefficients).val.drop $next) ($deltaFn $j)))
            simp only [← ($prev).property]
            dsimp only [$prev:ident]
            simp only [← ($delta).property]
            dsimp only [$delta:ident, $coefficients:ident]
            cbv)
      declarations := declarations.push declaration
    let localValue := Lean.mkIdent (.mkSimple ("local" ++ side ++ index))
    let stage := Lean.mkIdent (.mkSimple ("local" ++ side ++ index ++ "Stage0"))
    let localFn := Lean.mkIdent
      (if side == "Lo" then ``Enclosure.localLo else ``Enclosure.localHi)
    declarations := declarations.push (← `(command|
      abbrev $localValue : {v // v = $localFn $j} :=
        ⟨($stage).val, ($stage).property.trans
          (congrArg (fun p => Enclosure.polyComp p ($deltaFn $j)) ($coefficients).property)⟩))
    let endpoint := Lean.mkIdent (.mkSimple ("endpoint" ++ side ++ index))
    let endpointFn := Lean.mkIdent
      (if side == "Lo" then ``Enclosure.endpointLo else ``Enclosure.endpointHi)
    let density ← if side == "Lo" then `(term| (0.0432139182637 : ℚ))
      else `(term| (0.0432139182638 : ℚ))
    let gibbs := Lean.mkIdent (.mkSimple ("gibbs" ++ side ++ index))
    declarations := declarations.push (← `(command|
      abbrev $gibbs : {v // v = Enclosure.polyMul
          [Enclosure.mul (Enclosure.point $density) ($endpointFn $j)] ($localFn $j)} := by
        certify_first_atom =>
          simp only [← ($endpoint).property]
          dsimp only [$endpoint:ident]
          simp only [← ($localValue).property]
          dsimp only [$localValue:ident, $stage:ident]
          cbv))
    let orders := if side == "Lo" then [0, 1, 2] else [1, 3]
    for r in orders do
      let order := Lean.Syntax.mkNumLit (toString r)
      let suffix := side ++ toString r ++ "_" ++ index
      let prefactor := Lean.mkIdent (.mkSimple ("prefactor" ++ suffix))
      let source := Lean.mkIdent (.mkSimple ("source" ++ side ++ index))
      let sourceFn := Lean.mkIdent
        (if side == "Lo" then ``Enclosure.sourceLo else ``Enclosure.sourceHi)
      let coefficient ← if side == "Lo" then `(term| (12.5663706143591729538 : ℚ))
        else `(term| (12.5663706143591729539 : ℚ))
      declarations := declarations.push (← `(command|
        abbrev $prefactor : {v // v = Enclosure.polyMul
            (Enclosure.polyMul [Enclosure.point $coefficient]
              (Enclosure.polyPow
                (Enclosure.polyAdd [Enclosure.point ((($j : ℕ) : ℚ) / 64)]
                  (Enclosure.polyPoint X)) (2 * $order))) ($sourceFn $j)} := by
          certify_first_atom =>
            simp only [← ($source).property]
            dsimp only [$source:ident]
            cbv))
      let polynomial := Lean.mkIdent (.mkSimple ("polynomial" ++ suffix))
      let polynomialFn := Lean.mkIdent
        (if side == "Lo" then ``Enclosure.polynomialLo else ``Enclosure.polynomialHi)
      declarations := declarations.push (← `(command|
        abbrev $polynomial : {v // v = $polynomialFn $order $j} := by
          certify_first_atom =>
            rw [$polynomialFn:ident]
            simp only [← ($prefactor).property]
            dsimp only [$prefactor:ident]
            simp only [← ($gibbs).property]
            dsimp only [$gibbs:ident]
            cbv))
      let mass := Lean.mkIdent (.mkSimple ("mass" ++ suffix))
      let massFn := Lean.mkIdent
        (if side == "Lo" then ``Enclosure.massLo else ``Enclosure.massHi)
      let length := (if side == "Lo" then 54 else 42) + 2 * r
      let mut widths := #[]
      for k in [1:length + 1] do
        let width := Lean.mkIdent (.mkSimple ("widthPower" ++ toString k))
        widths := widths.push (← `(Lean.Parser.Tactic.simpLemma| ← ($width).property))
      declarations := declarations.push (← `(command|
        abbrev $mass : {v // v = $massFn $order $j} := by
          certify_first_atom =>
            rw [$massFn:ident]
            simp only [← ($polynomial).property]
            dsimp only [$polynomial:ident]
            simp only [Enclosure.mass, Nat.reduceAdd, $[$widths],*]
            cbv))
      let raw := Lean.mkIdent (.mkSimple ("raw" ++ suffix))
      let projection := Lean.mkIdent
        (if side == "Lo" then ``Enclosure.Bounds.lo else ``Enclosure.Bounds.hi)
      declarations := declarations.push (← `(command|
        abbrev $raw : {v // v = $projection ($massFn $order $j)} := by
          certify_first_atom =>
            simp only [← ($mass).property]
            dsimp only [$mass:ident]
            cbv))
  return ⟨Lean.mkNullNode declarations⟩

end RHTower.ThetaRationalQuadrature.Certificates
