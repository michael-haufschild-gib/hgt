/-
Testing the displacement framework against the most recent exponent pairs.

The systematic optimisation of the exponent database records the pairs

    P₁ = (10769/351096, 609317/702192) ,      P₂ = (89/3478, 15327/17390) .

Unlike every earlier landmark, both lie **off** the line of symmetry: their displacements are
`236683/702192 ≈ 0.3371` and `6187/17390 ≈ 0.3558`.  So they are exactly the kind of object the
displacement framework says could matter — a record family is only helped by pairs with nonzero
displacement.

Their pointwise exponents are `93253/468128 ≈ 0.1992` and `7077/34780 ≈ 0.2035`, both far above
`13/84 ≈ 0.1548`.  Feeding these into the cost formula `ρ = (μ - θ)/d` gives costs of about `0.1319`
and `0.1369`, against `167/1764 ≈ 0.0947` for the `A`-image of the record pair.  Their efficiency
thresholds are therefore about `0.368` and `0.363`, below the record pair's `715/1764 ≈ 0.4053`.

**So the newest pairs, despite being off the line, buy displacement more expensively than the
`A`-process does at the record, and do not extend the productive range.**  The framework's prediction
— that only a low displacement cost matters, not displacement itself — survives contact with the most
recent data.
-/
import GaloisForLFunctions.HTGeometry.DisplacementCostAndFaces

namespace HTGeometry

/-! ### The two recent pairs -/

/-- First coordinate of the first recent pair. -/
def ttyPair1Kappa : ℚ := 10769 / 351096

/-- Second coordinate of the first recent pair. -/
def ttyPair1Lambda : ℚ := 609317 / 702192

/-- First coordinate of the second recent pair. -/
def ttyPair2Kappa : ℚ := 89 / 3478

/-- Second coordinate of the second recent pair. -/
def ttyPair2Lambda : ℚ := 15327 / 17390

/-! ### They are off the line of symmetry -/

/-- **The first recent pair has displacement `236683/702192`.** -/
theorem ttyPair1_displacement :
    epDisplacement ttyPair1Kappa ttyPair1Lambda = 236683 / 702192 := by
  unfold epDisplacement ttyPair1Kappa ttyPair1Lambda; norm_num

/-- **The second recent pair has displacement `6187/17390`.** -/
theorem ttyPair2_displacement :
    epDisplacement ttyPair2Kappa ttyPair2Lambda = 6187 / 17390 := by
  unfold epDisplacement ttyPair2Kappa ttyPair2Lambda; norm_num

/-- **Both are strictly off the line**, unlike every landmark pair. -/
theorem tty_pairs_offline :
    0 < epDisplacement ttyPair1Kappa ttyPair1Lambda ∧
      0 < epDisplacement ttyPair2Kappa ttyPair2Lambda := by
  rw [ttyPair1_displacement, ttyPair2_displacement]
  constructor <;> norm_num

/-- Their displacements exceed that of the `A`-image of the record pair. -/
theorem tty_displacements_exceed_procA :
    epDisplacement (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        < epDisplacement ttyPair1Kappa ttyPair1Lambda ∧
      epDisplacement (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        < epDisplacement ttyPair2Kappa ttyPair2Lambda := by
  rw [procA_bourgain_displacement, ttyPair1_displacement, ttyPair2_displacement]
  constructor <;> norm_num

/-! ### But their pointwise exponents are far from the record -/

/-- The first recent pair's pointwise exponent. -/
theorem ttyPair1_mu : epMu ttyPair1Kappa ttyPair1Lambda = 93253 / 468128 := by
  unfold epMu ttyPair1Kappa ttyPair1Lambda; norm_num

/-- The second recent pair's pointwise exponent. -/
theorem ttyPair2_mu : epMu ttyPair2Kappa ttyPair2Lambda = 7077 / 34780 := by
  unfold epMu ttyPair2Kappa ttyPair2Lambda; norm_num

/-- **Neither improves the subconvexity record.** -/
theorem tty_pairs_do_not_beat_record :
    bourgainTheta < epMu ttyPair1Kappa ttyPair1Lambda ∧
      bourgainTheta < epMu ttyPair2Kappa ttyPair2Lambda := by
  rw [ttyPair1_mu, ttyPair2_mu]
  constructor <;> (unfold bourgainTheta; norm_num)

/-- Both exponents also exceed that of the `A`-image of the record pair. -/
theorem tty_mu_exceeds_procA :
    epMu (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        < epMu ttyPair1Kappa ttyPair1Lambda ∧
      epMu (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        < epMu ttyPair2Kappa ttyPair2Lambda := by
  rw [procA_bourgain_mu, ttyPair1_mu, ttyPair2_mu]
  constructor <;> norm_num

/-! ### Their displacement costs are higher, so their thresholds are lower -/

/-- **The first recent pair's displacement cost exceeds the `A`-image's.** -/
theorem ttyPair1_cost_exceeds :
    displacementCost (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        bourgainTheta < displacementCost ttyPair1Kappa ttyPair1Lambda bourgainTheta := by
  rw [procA_bourgain_cost]
  unfold displacementCost
  rw [ttyPair1_mu, ttyPair1_displacement]
  unfold bourgainTheta
  norm_num

/-- **And so does the second's.** -/
theorem ttyPair2_cost_exceeds :
    displacementCost (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        bourgainTheta < displacementCost ttyPair2Kappa ttyPair2Lambda bourgainTheta := by
  rw [procA_bourgain_cost]
  unfold displacementCost
  rw [ttyPair2_mu, ttyPair2_displacement]
  unfold bourgainTheta
  norm_num

/-- **Hence both efficiency thresholds fall below the `A`-process's productivity threshold.**  The
newest pairs do not extend the range over which the exponent-pair machinery is productive. -/
theorem tty_thresholds_below_productivity :
    efficiencyThreshold ttyPair1Kappa ttyPair1Lambda bourgainTheta < bourgainAThreshold ∧
      efficiencyThreshold ttyPair2Kappa ttyPair2Lambda bourgainTheta < bourgainAThreshold := by
  rw [← procA_bourgain_threshold, threshold_eq_half_sub_cost, threshold_eq_half_sub_cost,
    threshold_eq_half_sub_cost]
  constructor
  · linarith [ttyPair1_cost_exceeds]
  · linarith [ttyPair2_cost_exceeds]

/-- Both thresholds also fall below the published handoff length, so neither pair is productive
anywhere the published proof would use it. -/
theorem tty_thresholds_below_handoff :
    efficiencyThreshold ttyPair1Kappa ttyPair1Lambda bourgainTheta < decouplingStart ∧
      efficiencyThreshold ttyPair2Kappa ttyPair2Lambda bourgainTheta < decouplingStart := by
  unfold efficiencyThreshold decouplingStart
  rw [ttyPair1_mu, ttyPair1_displacement, ttyPair2_mu, ttyPair2_displacement]
  unfold bourgainTheta
  constructor <;> norm_num

/-- **The framework's prediction, tested.**  Displacement alone is not the resource; the resource is
displacement *per unit of surrendered exponent*.  The newest pairs have larger displacement than the
`A`-image of the record pair and are nevertheless less useful, because their exponents are further
from the record. -/
theorem displacement_alone_is_not_the_resource :
    epDisplacement (procA_fst bourgainKappa) (procA_snd bourgainKappa bourgainLambda)
        < epDisplacement ttyPair1Kappa ttyPair1Lambda ∧
      efficiencyThreshold ttyPair1Kappa ttyPair1Lambda bourgainTheta
        < efficiencyThreshold (procA_fst bourgainKappa)
          (procA_snd bourgainKappa bourgainLambda) bourgainTheta :=
  ⟨tty_displacements_exceed_procA.1, by
    rw [threshold_eq_half_sub_cost, threshold_eq_half_sub_cost]
    linarith [ttyPair1_cost_exceeds]⟩

end HTGeometry
