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
      -- One scaled row is added at a time, preserving the exact convolution order.
      let rows := (if side == "Lo" then 9 else 10) + 2 * r
      for offset in [:rows + 1] do
        let k := rows - offset
        let n := Lean.Syntax.mkNumLit (toString k)
        let row := Lean.mkIdent (.mkSimple ("product" ++ suffix ++ "Row" ++ toString k))
        let declaration ← if k == rows then
          `(command| abbrev $row : {v // v = Enclosure.polyMul
              (($prefactor).val.drop $n) ($gibbs).val} := by
            certify_first_atom =>
              change ([] : List Enclosure.Bounds)
              cbv)
        else do
          let next := Lean.Syntax.mkNumLit (toString (k + 1))
          let prev := Lean.mkIdent
            (.mkSimple ("product" ++ suffix ++ "Row" ++ toString (k + 1)))
          `(command| abbrev $row : {v // v = Enclosure.polyMul
              (($prefactor).val.drop $n) ($gibbs).val} := by
            certify_first_atom =>
              change Enclosure.polyAdd
                (Enclosure.polyScale
                  ((($prefactor).val[$n]?).getD (Enclosure.point 0)) ($gibbs).val)
                (Enclosure.point 0 :: Enclosure.polyMul
                  (($prefactor).val.drop $next) ($gibbs).val)
              simp only [← ($prev).property]
              dsimp only [$prev:ident, $prefactor:ident, $gibbs:ident]
              cbv)
        declarations := declarations.push declaration
      let product := Lean.mkIdent (.mkSimple ("product" ++ suffix ++ "Row0"))
      declarations := declarations.push (← `(command|
        abbrev $polynomial : {v // v = $polynomialFn $order $j} :=
          ⟨($product).val, ($product).property.trans
            (congrArg₂ Enclosure.polyMul ($prefactor).property ($gibbs).property)⟩))
      let mass := Lean.mkIdent (.mkSimple ("mass" ++ suffix))
      let massFn := Lean.mkIdent
        (if side == "Lo" then ``Enclosure.massLo else ``Enclosure.massHi)
      let length := (if side == "Lo" then 54 else 42) + 2 * r
      -- Integration follows polynomial tails of at most eight coefficients.
      let blocks := (length + 7) / 8
      for offset in [:blocks + 1] do
        let k := min length ((blocks - offset) * 8)
        let degree := Lean.Syntax.mkNumLit (toString k)
        let tail := Lean.mkIdent (.mkSimple ("integral" ++ suffix ++ "Tail" ++ toString k))
        let declaration ← if k == length then
          `(command| abbrev $tail : {v // v = Enclosure.mass
              (($polynomial).val.drop $degree) $degree (Enclosure.point (1 / 64))} := by
            certify_first_atom =>
              change Enclosure.point 0
              cbv)
        else do
          let finish := min length (k + 8)
          let nextDegree := Lean.Syntax.mkNumLit (toString finish)
          let nextTail := Lean.mkIdent
            (.mkSimple ("integral" ++ suffix ++ "Tail" ++ toString finish))
          let mut expression ← `(term| Enclosure.mass
            (($polynomial).val.drop $nextDegree) $nextDegree (Enclosure.point (1 / 64)))
          let mut widths := #[]
          let mut widthValues := #[]
          for offset in [:finish - k] do
            let position := finish - offset - 1
            let coefficientIndex := Lean.Syntax.mkNumLit (toString position)
            let exponent := Lean.Syntax.mkNumLit (toString (position + 1))
            expression ← `(term| Enclosure.add
              (Enclosure.divNat
                (Enclosure.mul
                  ((($polynomial).val[$coefficientIndex]?).getD (Enclosure.point 0))
                  (Enclosure.pow (Enclosure.point (1 / 64)) $exponent)) $exponent)
              $expression)
            let width := Lean.mkIdent (.mkSimple ("widthPower" ++ toString (position + 1)))
            widths := widths.push (← `(Lean.Parser.Tactic.simpLemma| ← ($width).property))
            widthValues := widthValues.push (← `(Lean.Parser.Tactic.simpLemma| $width:ident))
          `(command| abbrev $tail : {v // v = Enclosure.mass
              (($polynomial).val.drop $degree) $degree (Enclosure.point (1 / 64))} := by
            certify_first_atom =>
              change $expression
              simp only [← ($nextTail).property]
              dsimp only [$nextTail:ident, $polynomial:ident, $product:ident]
              simp only [$[$widths],*]
              dsimp only [$[$widthValues],*]
              cbv)
        declarations := declarations.push declaration
      let integral := Lean.mkIdent (.mkSimple ("integral" ++ suffix ++ "Tail0"))
      declarations := declarations.push (← `(command|
        abbrev $mass : {v // v = $massFn $order $j} :=
          ⟨($integral).val, ($integral).property.trans
            (congrArg (fun p => Enclosure.mass p 0 (Enclosure.point (1 / 64)))
              ($polynomial).property)⟩))
      let raw := Lean.mkIdent (.mkSimple ("raw" ++ suffix))
      let projection := Lean.mkIdent
        (if side == "Lo" then ``Enclosure.Bounds.lo else ``Enclosure.Bounds.hi)
      declarations := declarations.push (← `(command|
        abbrev $raw : {v // v = $projection ($massFn $order $j)} := by
          certify_first_atom =>
            simp only [← ($mass).property]
            dsimp only [$mass:ident, $integral:ident]
            cbv))
  return ⟨Lean.mkNullNode declarations⟩

end RHTower.ThetaRationalQuadrature.Certificates
