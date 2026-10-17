import GaloisForLFunctions.RHTower.CHMDOddBoundStateSignObstructionAndParityQuarterBound
import GaloisForLFunctions.RHTower.CHMDJumpGraphContractions
import GaloisForLFunctions.RHTower.CHMDBoundStateDimension

/-!
# Beurling–Deny Nodal Decomposition, Strict Cross-Jump Irreducibility, and Parity Bound-State Spaces

This module formalises the Beurling–Deny normal contractions `posGraph`, `negGraph`, `absGraph` on
the closed Doob jump graph `SourceGraph`, proves the exact cross-jump energy identity
`sourceEnergy (absGraph p) = sourceEnergy p + 4 * sourcePair (posGraph p) (negGraph p)`,
establishes the odd-to-even Beurling–Deny energy bridge
`sourceEnergy p = weilForm (absGraph p) - 2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 - 4 * sourcePair (posGraph p) (negGraph p)`,
proves strict archimedean cross-jump irreducibility (`sourcePair (posGraph p) (negGraph p) = 0 ↔ posGraph p = 0 ∨ negGraph p = 0`)
and the Courant nodal Rayleigh-quotient boost for primitive eigenvectors, and decomposes
`boundStateSpace` into orthogonal parity subspaces `evenBoundStateSpace ⊔ oddBoundStateSpace`
with unconditional dimension bounds `#(quarterZeros) + 1` and `#(quarterZeros)`.
-/

open MeasureTheory Set Filter Topology Zeta23
open scoped InnerProductSpace
noncomputable section
namespace RHTower.CHMDPolar
open CHMDDoobGraph CHMDClosedJump

/-! ## Section 1: Normal Contractions `posGraph`, `negGraph`, `absGraph` and the Exact Beurling–Deny Cross-Jump Formula -/

def posFun (x : ℝ) : ℝ := max x 0
def negFun (x : ℝ) : ℝ := max (-x) 0
def absFun (x : ℝ) : ℝ := |x|

theorem lipschitz_posFun : LipschitzWith 1 posFun :=
  LipschitzWith.id.max_const 0

theorem lipschitz_negFun : LipschitzWith 1 negFun :=
  LipschitzWith.id.neg.max_const 0

theorem lipschitz_absFun : LipschitzWith 1 absFun := by
  intro x y
  simp only [ENNReal.coe_one, one_mul, edist_dist, Real.dist_eq, absFun]
  exact ENNReal.ofReal_le_ofReal (abs_abs_sub_abs_le_abs_sub x y)

theorem posFun_zero : posFun 0 = 0 := max_self 0
theorem negFun_zero : negFun 0 = 0 := by simp [negFun]
theorem absFun_zero : absFun 0 = 0 := abs_zero

theorem posFun_nonneg (x : ℝ) : 0 ≤ posFun x := le_max_right x 0
theorem negFun_nonneg (x : ℝ) : 0 ≤ negFun x := le_max_right (-x) 0

theorem posFun_neg (x : ℝ) : posFun (-x) = negFun x := rfl
theorem negFun_neg (x : ℝ) : negFun (-x) = posFun x := by simp [negFun, posFun]
theorem absFun_neg (x : ℝ) : absFun (-x) = absFun x := abs_neg x

/-- Positive-part normal contraction on `SourceGraph`. -/
def posGraph (p : SourceGraph) : SourceGraph :=
  contract massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    lipschitz_posFun posFun_zero

/-- Negative-part normal contraction on `SourceGraph`. -/
def negGraph (p : SourceGraph) : SourceGraph :=
  contract massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    lipschitz_negFun negFun_zero

/-- Absolute-value normal contraction on `SourceGraph`. -/
def absGraph (p : SourceGraph) : SourceGraph :=
  contract massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    lipschitz_absFun absFun_zero

theorem posGraph_fst_ae (p : SourceGraph) :
    (posGraph p).val.fst =ᵐ[massMeasure] fun x => posFun (p.val.fst x) :=
  contract_source_ae massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    lipschitz_posFun posFun_zero

theorem negGraph_fst_ae (p : SourceGraph) :
    (negGraph p).val.fst =ᵐ[massMeasure] fun x => negFun (p.val.fst x) :=
  contract_source_ae massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    lipschitz_negFun negFun_zero

theorem absGraph_fst_ae (p : SourceGraph) :
    (absGraph p).val.fst =ᵐ[massMeasure] fun x => absFun (p.val.fst x) :=
  contract_source_ae massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    lipschitz_absFun absFun_zero

theorem posGraph_snd_ae (p : SourceGraph) :
    (posGraph p).val.snd =ᵐ[edgeMeasure]
      fun e => posFun (p.val.fst (left e)) - posFun (p.val.fst (right e)) :=
  contract_edge_ae massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    lipschitz_posFun posFun_zero

theorem negGraph_snd_ae (p : SourceGraph) :
    (negGraph p).val.snd =ᵐ[edgeMeasure]
      fun e => negFun (p.val.fst (left e)) - negFun (p.val.fst (right e)) :=
  contract_edge_ae massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    lipschitz_negFun negFun_zero

theorem absGraph_snd_ae (p : SourceGraph) :
    (absGraph p).val.snd =ᵐ[edgeMeasure]
      fun e => absFun (p.val.fst (left e)) - absFun (p.val.fst (right e)) :=
  contract_edge_ae massMeasure edgeMeasure left right nonsingular_left nonsingular_right p
    lipschitz_absFun absFun_zero

theorem posFun_sub_negFun (x : ℝ) : posFun x - negFun x = x := by
  unfold posFun negFun
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), sub_zero]
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_sub, neg_neg]

theorem posFun_add_negFun (x : ℝ) : posFun x + negFun x = absFun x := by
  unfold posFun negFun absFun
  rcases le_total 0 x with hx | hx
  · rw [max_eq_left hx, max_eq_right (neg_nonpos.mpr hx), add_zero, abs_of_nonneg hx]
  · rw [max_eq_right hx, max_eq_left (neg_nonneg.mpr hx), zero_add, abs_of_nonpos hx]

theorem posFun_mul_negFun (x : ℝ) : posFun x * negFun x = 0 := by
  unfold posFun negFun
  rcases le_total 0 x with hx | hx
  · rw [max_eq_right (neg_nonpos.mpr hx), mul_zero]
  · rw [max_eq_right hx, zero_mul]

theorem posFun_diff_mul_negFun_diff (a b : ℝ) :
    (posFun a - posFun b) * (negFun a - negFun b) =
      -(posFun a * negFun b + negFun a * posFun b) := by
  have ha := posFun_mul_negFun a
  have hb := posFun_mul_negFun b
  linarith

theorem posGraph_sub_negGraph (p : SourceGraph) : posGraph p - negGraph p = p := by
  apply source_projection_injective
  rw [Lp.ext_iff]
  filter_upwards [Lp.coeFn_sub (posGraph p).val.fst (negGraph p).val.fst,
    posGraph_fst_ae p, negGraph_fst_ae p] with x hsub hp hn
  change ((posGraph p).val.fst - (negGraph p).val.fst) x = p.val.fst x
  rw [hsub, Pi.sub_apply, hp, hn, posFun_sub_negFun]

theorem posGraph_add_negGraph (p : SourceGraph) : posGraph p + negGraph p = absGraph p := by
  apply source_projection_injective
  rw [Lp.ext_iff]
  filter_upwards [Lp.coeFn_add (posGraph p).val.fst (negGraph p).val.fst,
    posGraph_fst_ae p, negGraph_fst_ae p, absGraph_fst_ae p] with x hadd hp hn ha
  change ((posGraph p).val.fst + (negGraph p).val.fst) x = (absGraph p).val.fst x
  rw [hadd, Pi.add_apply, hp, hn, ha, posFun_add_negFun]

theorem inner_posGraph_negGraph_fst (p : SourceGraph) :
    ⟪(posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ = 0 := by
  rw [L2.inner_def]
  have h : (fun x => inner ℝ ((posGraph p).val.fst x) ((negGraph p).val.fst x)) =ᵐ[massMeasure]
      fun _ => (0 : ℝ) := by
    filter_upwards [posGraph_fst_ae p, negGraph_fst_ae p] with x hp hn
    simp only [RCLike.inner_apply, conj_trivial, hp, hn]
    rw [mul_comm, posFun_mul_negFun]
  rw [integral_congr_ae h, integral_zero]

theorem norm_absGraph_fst_sq (p : SourceGraph) :
    ‖(absGraph p).val.fst‖ ^ 2 = ‖p.val.fst‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq, L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [absGraph_fst_ae p] with x ha
  simp only [RCLike.inner_apply, conj_trivial, ha, absFun, ← sq, sq_abs]

theorem norm_absGraph_fst (p : SourceGraph) :
    ‖(absGraph p).val.fst‖ = ‖p.val.fst‖ :=
  (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp (norm_absGraph_fst_sq p)

theorem norm_posGraph_add_norm_negGraph_fst_sq (p : SourceGraph) :
    ‖(posGraph p).val.fst‖ ^ 2 + ‖(negGraph p).val.fst‖ ^ 2 = ‖p.val.fst‖ ^ 2 := by
  have h := congrArg (fun q : SourceGraph => ‖q.val.fst‖ ^ 2) (posGraph_sub_negGraph p)
  change ‖(posGraph p).val.fst - (negGraph p).val.fst‖ ^ 2 = ‖p.val.fst‖ ^ 2 at h
  rw [← real_inner_self_eq_norm_sq ((posGraph p).val.fst - (negGraph p).val.fst),
    inner_sub_left, inner_sub_right, inner_sub_right,
    real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq,
    real_inner_comm (posGraph p).val.fst (negGraph p).val.fst,
    inner_posGraph_negGraph_fst] at h
  linarith

theorem inner_posGraph_negGraph_snd_eq (p : SourceGraph) :
    ⟪(posGraph p).val.snd, (negGraph p).val.snd⟫_ℝ =
      -∫ e, (posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
        negFun (p.val.fst (left e)) * posFun (p.val.fst (right e))) ∂edgeMeasure := by
  rw [L2.inner_def, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [posGraph_snd_ae p, negGraph_snd_ae p] with e hp hn
  simp only [RCLike.inner_apply, conj_trivial, hp, hn]
  rw [mul_comm, posFun_diff_mul_negFun_diff]

theorem inner_posGraph_negGraph_snd_nonpos (p : SourceGraph) :
    ⟪(posGraph p).val.snd, (negGraph p).val.snd⟫_ℝ ≤ 0 := by
  rw [inner_posGraph_negGraph_snd_eq]
  have hpos : 0 ≤ ∫ e, (posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
      negFun (p.val.fst (left e)) * posFun (p.val.fst (right e))) ∂edgeMeasure := by
    refine integral_nonneg fun e => add_nonneg
      (mul_nonneg (posFun_nonneg _) (negFun_nonneg _))
      (mul_nonneg (negFun_nonneg _) (posFun_nonneg _))
  linarith

theorem sourcePair_posGraph_negGraph_eq_inner_snd (p : SourceGraph) :
    sourcePair (posGraph p) (negGraph p) =
      ⟪(posGraph p).val.snd, (negGraph p).val.snd⟫_ℝ := by
  change ⟪(posGraph p).val.snd, (negGraph p).val.snd⟫_ℝ -
    ⟪(posGraph p).val.fst, (negGraph p).val.fst⟫_ℝ = _
  rw [inner_posGraph_negGraph_fst, sub_zero]

theorem sourcePair_posGraph_negGraph_nonpos (p : SourceGraph) :
    sourcePair (posGraph p) (negGraph p) ≤ 0 := by
  rw [sourcePair_posGraph_negGraph_eq_inner_snd]
  exact inner_posGraph_negGraph_snd_nonpos p

theorem sourcePair_add_right (p q r : SourceGraph) :
    sourcePair p (q + r) = sourcePair p q + sourcePair p r := by
  rw [sourcePair_symm, sourcePair_add_left, sourcePair_symm q p, sourcePair_symm r p]

theorem sourcePair_sub_right (p q r : SourceGraph) :
    sourcePair p (q - r) = sourcePair p q - sourcePair p r := by
  rw [sourcePair_symm, sourcePair_sub_left, sourcePair_symm q p, sourcePair_symm r p]

/-- **Exact Beurling–Deny Nodal Decomposition of `sourceEnergy`.** -/
theorem sourceEnergy_eq_posGraph_add_negGraph_sub_two_sourcePair (p : SourceGraph) :
    sourceEnergy p =
      sourceEnergy (posGraph p) + sourceEnergy (negGraph p) -
        2 * sourcePair (posGraph p) (negGraph p) := by
  have hsub := posGraph_sub_negGraph p
  have h1 : sourceEnergy p = sourcePair (posGraph p - negGraph p) (posGraph p - negGraph p) := by
    rw [hsub, sourcePair_self]
  rw [h1, sourcePair_sub_left, sourcePair_sub_right, sourcePair_sub_right,
    sourcePair_self, sourcePair_self, sourcePair_symm (negGraph p) (posGraph p)]
  ring

/-- **Exact Beurling–Deny Cross-Jump Formula for `sourceEnergy (absGraph p)`.** -/
theorem sourceEnergy_absGraph_eq (p : SourceGraph) :
    sourceEnergy (absGraph p) =
      sourceEnergy p + 4 * sourcePair (posGraph p) (negGraph p) := by
  have hadd := posGraph_add_negGraph p
  have h1 : sourceEnergy (absGraph p) =
      sourcePair (posGraph p + negGraph p) (posGraph p + negGraph p) := by
    rw [hadd, sourcePair_self]
  rw [h1, sourcePair_add_left, sourcePair_add_right, sourcePair_add_right,
    sourcePair_self, sourcePair_self, sourcePair_symm (negGraph p) (posGraph p),
    sourceEnergy_eq_posGraph_add_negGraph_sub_two_sourcePair p]
  ring

/-- **Normal contraction lowers Doob energy:** `sourceEnergy (absGraph p) ≤ sourceEnergy p`. -/
theorem sourceEnergy_absGraph_le (p : SourceGraph) :
    sourceEnergy (absGraph p) ≤ sourceEnergy p := by
  rw [sourceEnergy_absGraph_eq]
  linarith [sourcePair_posGraph_negGraph_nonpos p]

theorem reflectGraph_posGraph (p : SourceGraph) :
    reflectGraph (posGraph p) = posGraph (reflectGraph p) := by
  apply source_projection_injective
  change (reflectGraph (posGraph p)).val.fst = (posGraph (reflectGraph p)).val.fst
  rw [reflectGraph_fst, Lp.ext_iff]
  have h1 := reflectMass_coeFn (posGraph p).val.fst
  have h2 := measurePreserving_neg_mass.quasiMeasurePreserving.ae_eq_comp (posGraph_fst_ae p)
  have h3 := posGraph_fst_ae (reflectGraph p)
  have h4 := reflectMass_coeFn p.val.fst
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  simp only [Function.comp_apply] at hx2
  rw [hx1, hx2, hx3, reflectGraph_fst, hx4]

theorem reflectGraph_negGraph (p : SourceGraph) :
    reflectGraph (negGraph p) = negGraph (reflectGraph p) := by
  apply source_projection_injective
  change (reflectGraph (negGraph p)).val.fst = (negGraph (reflectGraph p)).val.fst
  rw [reflectGraph_fst, Lp.ext_iff]
  have h1 := reflectMass_coeFn (negGraph p).val.fst
  have h2 := measurePreserving_neg_mass.quasiMeasurePreserving.ae_eq_comp (negGraph_fst_ae p)
  have h3 := negGraph_fst_ae (reflectGraph p)
  have h4 := reflectMass_coeFn p.val.fst
  filter_upwards [h1, h2, h3, h4] with x hx1 hx2 hx3 hx4
  simp only [Function.comp_apply] at hx2
  rw [hx1, hx2, hx3, reflectGraph_fst, hx4]

theorem reflectGraph_absGraph (p : SourceGraph) :
    reflectGraph (absGraph p) = absGraph (reflectGraph p) := by
  rw [← posGraph_add_negGraph, ← posGraph_add_negGraph, reflectGraph_add,
    reflectGraph_posGraph, reflectGraph_negGraph]

theorem posGraph_neg (p : SourceGraph) : posGraph (-p) = negGraph p := by
  apply source_projection_injective
  rw [Lp.ext_iff]
  have hneg : ((-p).val.fst : ℝ → ℝ) =ᵐ[massMeasure] fun x => -(p.val.fst x) :=
    Lp.coeFn_neg p.val.fst
  filter_upwards [posGraph_fst_ae (-p), negGraph_fst_ae p, hneg] with x hp hn hx
  rw [hp, hn, hx, posFun_neg]

theorem negGraph_neg (p : SourceGraph) : negGraph (-p) = posGraph p := by
  have h := posGraph_neg (-p)
  rw [neg_neg] at h
  exact h.symm

/-- For an odd graph vector `p`, its negative part is the reflection of its positive part. -/
theorem negGraph_eq_reflectGraph_posGraph_of_odd {p : SourceGraph} (hp : p.val.fst ∈ oddSector) :
    negGraph p = reflectGraph (posGraph p) := by
  rw [reflectGraph_posGraph, reflectGraph_eq_neg_of_odd hp, posGraph_neg]

/-- For an odd graph vector `p`, its absolute value contraction lies in the even sector. -/
theorem absGraph_fst_mem_evenSector_of_odd {p : SourceGraph} (hp : p.val.fst ∈ oddSector) :
    (absGraph p).val.fst ∈ evenSector := by
  rw [mem_evenSector, ← reflectGraph_fst, ← posGraph_add_negGraph,
    negGraph_eq_reflectGraph_posGraph_of_odd hp, reflectGraph_add,
    reflectGraph_reflectGraph, add_comm]

/-- **Odd-to-Even Beurling–Deny Energy Bridge.**
For every odd `p : SourceGraph`, the odd Doob energy `sourceEnergy p` equals the even-sector Weil
form `weilForm (absGraph p)` minus the ground-state square `2 ⟪|p|, 1⟫²` plus the nonnegative
cross-jump energy `-4 sourcePair (posGraph p) (negGraph p) ≥ 0`. -/
theorem sourceEnergy_odd_eq_weilForm_absGraph_sub {p : SourceGraph} (hp : p.val.fst ∈ oddSector) :
    sourceEnergy p =
      weilForm (absGraph p) - 2 * ⟪(absGraph p).val.fst, oneL⟫_ℝ ^ 2 -
        4 * sourcePair (posGraph p) (negGraph p) := by
  have heven := mem_evenSector.mp (absGraph_fst_mem_evenSector_of_odd hp)
  have htanh := inner_tanhL_eq_zero_of_even heven
  unfold weilForm
  rw [htanh, sourceEnergy_absGraph_eq]
  ring

/-! ## Section 2: Strict Archimedean Cross-Jump Irreducibility and Courant Nodal / Rayleigh Boost -/

/-- Strict positivity of the archimedean jump density forces one of `posGraph p` or `negGraph p`
to vanish whenever their cross-jump pairing vanishes. -/
theorem posGraph_eq_zero_or_negGraph_eq_zero_of_arch_cross_zero (f : ℝ → ℝ) (hf : Measurable f)
    (hzero : ∀ᵐ e ∂archMeasure,
      posFun (f (left e)) * negFun (f (right e)) +
        negFun (f (left e)) * posFun (f (right e)) = 0) :
    (∀ᵐ x ∂volume, posFun (f x) = 0) ∨ (∀ᵐ x ∂volume, negFun (f x) = 0) := by
  have hbase : ∀ᵐ e ∂archBase,
      posFun (f e.2) * negFun (f (e.2 + e.1)) = 0 ∧
      posFun (f (e.2 + e.1)) * negFun (f e.2) = 0 := by
    rw [archMeasure, ae_withDensity_iff measurable_archWeight.ennreal_ofReal] at hzero
    have ht : ∀ᵐ e ∂archBase, e.1 ∈ Ioi (0 : ℝ) :=
      Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Ioi)
    filter_upwards [hzero, ht] with e he ht'
    have h0 : posFun (f (left e)) * negFun (f (right e)) +
        negFun (f (left e)) * posFun (f (right e)) = 0 := by
      apply he
      apply (ENNReal.ofReal_pos.mpr _).ne'
      exact mul_pos (mul_pos (archLevyDensity_pos ht') (riemannKernelReal_pos _))
        (riemannKernelReal_pos _)
    have h1 : 0 ≤ posFun (f e.2) * negFun (f (e.2 + e.1)) :=
      mul_nonneg (posFun_nonneg _) (negFun_nonneg _)
    have h2 : 0 ≤ negFun (f e.2) * posFun (f (e.2 + e.1)) :=
      mul_nonneg (negFun_nonneg _) (posFun_nonneg _)
    change posFun (f e.2) * negFun (f (e.2 + e.1)) +
      negFun (f e.2) * posFun (f (e.2 + e.1)) = 0 at h0
    refine ⟨by linarith, ?_⟩
    rw [mul_comm]
    linarith
  have hsections := (ae_restrict_iff' measurableSet_Ioi).mp (Measure.ae_ae_of_ae_prod hbase)
  have hmp1 : Measurable fun p : ℝ × ℝ => posFun (f p.2) * negFun (f (p.2 + p.1)) :=
    ((lipschitz_posFun.continuous.measurable.comp hf).comp measurable_snd).mul
      ((lipschitz_negFun.continuous.measurable.comp hf).comp (measurable_snd.add measurable_fst))
  have hmp2 : Measurable fun p : ℝ × ℝ => posFun (f (p.2 + p.1)) * negFun (f p.2) :=
    ((lipschitz_posFun.continuous.measurable.comp hf).comp (measurable_snd.add measurable_fst)).mul
      ((lipschitz_negFun.continuous.measurable.comp hf).comp measurable_snd)
  have hproduct : ∀ᵐ e ∂(volume.prod volume : Measure (ℝ × ℝ)),
      0 < e.1 → posFun (f e.2) * negFun (f (e.2 + e.1)) = 0 ∧
        posFun (f (e.2 + e.1)) * negFun (f e.2) = 0 := by
    apply (Measure.ae_prod_iff_ae_ae
      ((measurableSet_lt measurable_const measurable_fst).imp
        ((measurableSet_eq_fun hmp1 measurable_const).inter
          (measurableSet_eq_fun hmp2 measurable_const)))).mpr
    filter_upwards [hsections] with t ht
    by_cases hp : 0 < t
    · exact (ht hp).mono fun x hx _ => hx
    · exact Eventually.of_forall fun _ hx => (hp hx).elim
  have hshear := Measure.measurePreserving_swap.comp
    (measurePreserving_prod_neg_add (volume : Measure ℝ) volume)
  have hordered : ∀ᵐ e ∂(volume.prod volume : Measure (ℝ × ℝ)),
      e.1 < e.2 → posFun (f e.1) * negFun (f e.2) = 0 ∧
        posFun (f e.2) * negFun (f e.1) = 0 := by
    filter_upwards [hshear.quasiMeasurePreserving.ae hproduct] with e he
    intro hlt
    have hh := he (by dsimp only [Function.comp_def, Prod.swap]; linarith)
    simpa only [Function.comp_def, Prod.swap, add_neg_cancel_left] using hh
  have hall : ∀ᵐ e ∂(volume.prod volume : Measure (ℝ × ℝ)),
      posFun (f e.1) * negFun (f e.2) = 0 := by
    filter_upwards [hordered, Measure.measurePreserving_swap.quasiMeasurePreserving.ae hordered]
      with e hforward hbackward
    rcases lt_trichotomy e.1 e.2 with hlt | heq | hgt
    · exact (hforward hlt).1
    · rw [heq]
      exact posFun_mul_negFun (f e.2)
    · exact (hbackward hgt).2
  have hae := Measure.ae_ae_of_ae_prod hall
  by_cases hpos : ∀ᵐ x ∂volume, posFun (f x) = 0
  · exact Or.inl hpos
  · right
    have hex : ∃ x, posFun (f x) ≠ 0 ∧ ∀ᵐ y ∂volume, posFun (f x) * negFun (f y) = 0 := by
      by_contra hno
      apply hpos
      filter_upwards [hae] with x hx
      by_contra hne
      exact hno ⟨x, hne, hx⟩
    obtain ⟨x, hxne, hxy⟩ := hex
    filter_upwards [hxy] with y hy
    exact (mul_eq_zero.mp hy).resolve_left hxne

theorem integrable_crossJump (p : SourceGraph) :
    Integrable (fun e => posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
      negFun (p.val.fst (left e)) * posFun (p.val.fst (right e))) edgeMeasure := by
  have hint := L2.integrable_inner (𝕜 := ℝ) (posGraph p).val.snd (negGraph p).val.snd
  have hcongr : (fun e => -inner ℝ ((posGraph p).val.snd e) ((negGraph p).val.snd e)) =ᵐ[edgeMeasure]
      fun e => posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
        negFun (p.val.fst (left e)) * posFun (p.val.fst (right e)) := by
    filter_upwards [posGraph_snd_ae p, negGraph_snd_ae p] with e hp hn
    simp only [RCLike.inner_apply, conj_trivial, hp, hn]
    rw [mul_comm, posFun_diff_mul_negFun_diff, neg_neg]
  exact hint.neg.congr hcongr

/-- **Strict Archimedean Irreducibility of the Cross-Jump Pairing.**
The cross-jump pairing `sourcePair (posGraph p) (negGraph p)` vanishes if and only if `p` does not
change sign on `ℝ` (`posGraph p = 0 ∨ negGraph p = 0`). -/
theorem sourcePair_posGraph_negGraph_eq_zero_iff (p : SourceGraph) :
    sourcePair (posGraph p) (negGraph p) = 0 ↔ posGraph p = 0 ∨ negGraph p = 0 := by
  constructor
  · intro h0
    rw [sourcePair_posGraph_negGraph_eq_inner_snd, inner_posGraph_negGraph_snd_eq, neg_eq_zero] at h0
    have hae : ∀ᵐ e ∂edgeMeasure,
        posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
          negFun (p.val.fst (left e)) * posFun (p.val.fst (right e)) = 0 := by
      exact (integral_eq_zero_iff_of_nonneg_ae
        (Eventually.of_forall fun e => add_nonneg
          (mul_nonneg (posFun_nonneg _) (negFun_nonneg _))
          (mul_nonneg (negFun_nonneg _) (posFun_nonneg _)))
        (integrable_crossJump p)).mp h0
    have harch : ∀ᵐ e ∂archMeasure,
        posFun (p.val.fst (left e)) * negFun (p.val.fst (right e)) +
          negFun (p.val.fst (left e)) * posFun (p.val.fst (right e)) = 0 :=
      (ae_add_measure_iff.mp hae).1
    rcases posGraph_eq_zero_or_negGraph_eq_zero_of_arch_cross_zero p.val.fst
      (Lp.stronglyMeasurable p.val.fst).measurable harch with hp | hn
    · left
      apply source_projection_injective
      rw [Lp.ext_iff]
      filter_upwards [posGraph_fst_ae p, (withDensity_absolutelyContinuous volume _).ae_eq hp,
        Lp.coeFn_zero ℝ 2 massMeasure] with x hx1 hx2 hx0
      change (posGraph p).val.fst x = (0 : MassSpace) x
      rw [hx1, hx2, hx0, Pi.zero_apply]
    · right
      apply source_projection_injective
      rw [Lp.ext_iff]
      filter_upwards [negGraph_fst_ae p, (withDensity_absolutelyContinuous volume _).ae_eq hn,
        Lp.coeFn_zero ℝ 2 massMeasure] with x hx1 hx2 hx0
      change (negGraph p).val.fst x = (0 : MassSpace) x
      rw [hx1, hx2, hx0, Pi.zero_apply]
  · rintro (hp | hn)
    · rw [hp]
      change ⟪(0 : SourceGraph).val.snd, (negGraph p).val.snd⟫_ℝ -
        ⟪(0 : SourceGraph).val.fst, (negGraph p).val.fst⟫_ℝ = 0
      simp
    · rw [hn]
      change ⟪(posGraph p).val.snd, (0 : SourceGraph).val.snd⟫_ℝ -
        ⟪(posGraph p).val.fst, (0 : SourceGraph).val.fst⟫_ℝ = 0
      simp

theorem sourcePair_posGraph_negGraph_neg_of_ne_zero {p : SourceGraph}
    (hp : posGraph p ≠ 0) (hn : negGraph p ≠ 0) :
    sourcePair (posGraph p) (negGraph p) < 0 := by
  apply lt_of_le_of_ne (sourcePair_posGraph_negGraph_nonpos p)
  intro h0
  rcases (sourcePair_posGraph_negGraph_eq_zero_iff p).mp h0 with h | h
  · exact hp h
  · exact hn h

theorem sourceEnergy_absGraph_eq_iff (p : SourceGraph) :
    sourceEnergy (absGraph p) = sourceEnergy p ↔ posGraph p = 0 ∨ negGraph p = 0 := by
  rw [sourceEnergy_absGraph_eq, ← sourcePair_posGraph_negGraph_eq_zero_iff]
  constructor <;> intro h <;> linarith

theorem sourceEnergy_absGraph_lt_of_ne_zero {p : SourceGraph}
    (hp : posGraph p ≠ 0) (hn : negGraph p ≠ 0) :
    sourceEnergy (absGraph p) < sourceEnergy p := by
  rw [sourceEnergy_absGraph_eq]
  linarith [sourcePair_posGraph_negGraph_neg_of_ne_zero hp hn]

theorem inner_posGraph_oneL_nonneg (p : SourceGraph) :
    0 ≤ ⟪(posGraph p).val.fst, oneL⟫_ℝ := by
  rw [L2.inner_def]
  have h : 0 ≤ᵐ[massMeasure] fun x => inner ℝ ((posGraph p).val.fst x) (oneL x) := by
    have h1 : (oneL : ℝ → ℝ) =ᵐ[massMeasure] fun _ => (1 : ℝ) :=
      (memLp_const 1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp
    filter_upwards [posGraph_fst_ae p, h1] with x hp ho
    simp only [RCLike.inner_apply, conj_trivial, hp, ho, one_mul]
    exact posFun_nonneg _
  exact integral_nonneg_of_ae h

theorem inner_posGraph_oneL_eq_zero_iff (p : SourceGraph) :
    ⟪(posGraph p).val.fst, oneL⟫_ℝ = 0 ↔ posGraph p = 0 := by
  constructor
  · intro h0
    rw [L2.inner_def] at h0
    have h1 : (oneL : ℝ → ℝ) =ᵐ[massMeasure] fun _ => (1 : ℝ) :=
      (memLp_const 1 : MemLp (fun _ : ℝ => (1 : ℝ)) 2 massMeasure).coeFn_toLp
    have hnn : 0 ≤ᵐ[massMeasure] fun x => inner ℝ ((posGraph p).val.fst x) (oneL x) := by
      filter_upwards [posGraph_fst_ae p, h1] with x hp ho
      simp only [RCLike.inner_apply, conj_trivial, hp, ho, one_mul]
      exact posFun_nonneg _
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnn
      (L2.integrable_inner (𝕜 := ℝ) (posGraph p).val.fst oneL)).mp h0
    apply source_projection_injective
    rw [Lp.ext_iff]
    filter_upwards [hae, h1, Lp.coeFn_zero ℝ 2 massMeasure] with x hx ho hz
    simp only [RCLike.inner_apply, conj_trivial, ho, one_mul] at hx
    change (posGraph p).val.fst x = (0 : MassSpace) x
    rw [hx, hz, Pi.zero_apply]
  · intro hp
    rw [hp]
    exact inner_zero_left oneL

theorem inner_negGraph_oneL_eq_zero_iff (p : SourceGraph) :
    ⟪(negGraph p).val.fst, oneL⟫_ℝ = 0 ↔ negGraph p = 0 := by
  rw [← posGraph_neg, inner_posGraph_oneL_eq_zero_iff]

/-- Every nonzero primitive graph vector changes sign on `ℝ` (`posGraph p ≠ 0 ∧ negGraph p ≠ 0`). -/
theorem posGraph_ne_zero_and_negGraph_ne_zero_of_primitive {p : SourceGraph}
    (hp0 : p ≠ 0) (hprim : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    posGraph p ≠ 0 ∧ negGraph p ≠ 0 := by
  have hsub : (posGraph p).val.fst - (negGraph p).val.fst = p.val.fst :=
    congrArg (fun q : SourceGraph => q.val.fst) (posGraph_sub_negGraph p)
  have heq : ⟪(posGraph p).val.fst, oneL⟫_ℝ = ⟪(negGraph p).val.fst, oneL⟫_ℝ := by
    have h1 := congrArg (fun w : MassSpace => ⟪w, oneL⟫_ℝ) hsub
    rw [inner_sub_left, hprim] at h1
    linarith
  have hboth : posGraph p = 0 ↔ negGraph p = 0 := by
    rw [← inner_posGraph_oneL_eq_zero_iff, ← inner_negGraph_oneL_eq_zero_iff, heq]
  constructor
  · intro hp
    have hn := hboth.mp hp
    apply hp0
    rw [← posGraph_sub_negGraph p, hp, hn, sub_zero]
  · intro hn
    have hp := hboth.mpr hn
    apply hp0
    rw [← posGraph_sub_negGraph p, hp, hn, sub_zero]

/-- **Strict Beurling–Deny Energy Drop on Nonzero Primitive Graph Vectors.**
Every nonzero primitive graph vector (and in particular every nonzero odd graph vector) has
strictly lower Doob energy after absolute-value contraction:
`sourceEnergy (absGraph p) < sourceEnergy p`. -/
theorem sourceEnergy_absGraph_lt_of_primitive {p : SourceGraph}
    (hp0 : p ≠ 0) (hprim : ⟪p.val.fst, oneL⟫_ℝ = 0) :
    sourceEnergy (absGraph p) < sourceEnergy p := by
  obtain ⟨hp, hn⟩ := posGraph_ne_zero_and_negGraph_ne_zero_of_primitive hp0 hprim
  exact sourceEnergy_absGraph_lt_of_ne_zero hp hn

/-- Universal graph Cauchy–Schwarz inequality relating `sourceEnergy q` and `⟪resolvent u, u⟫`. -/
theorem norm_fst_pow_four_le_inner_resolvent_mul (q : SourceGraph) :
    ‖q.val.fst‖ ^ 4 ≤
      ⟪resolvent q.val.fst, q.val.fst⟫_ℝ * (sourceEnergy q + 2 * ‖q.val.fst‖ ^ 2) := by
  have h1 : ‖q.val.fst‖ ^ 2 ≤ ‖rieszLift q.val.fst‖ * ‖q‖ := by
    rw [← real_inner_self_eq_norm_sq, ← inner_rieszLift]
    exact real_inner_le_norm _ _
  have h2 : (‖q.val.fst‖ ^ 2) ^ 2 ≤ (‖rieszLift q.val.fst‖ * ‖q‖) ^ 2 :=
    pow_le_pow_left₀ (sq_nonneg _) h1 2
  rw [← pow_mul, mul_pow, ← inner_resolvent_self, ← sourceEnergy_add_two_mass] at h2
  exact h2

/-- **Courant Nodal Energy Identity on the Positive Part of an Eigenvector.** -/
theorem sourceEnergy_posGraph_rieszLift_of_eigenvector {μ : ℝ} (hμ : μ ≠ 0) {w : MassSpace}
    (heig : resolvent w = μ • w) :
    sourceEnergy (posGraph (rieszLift w)) =
      ((1 - 2 * μ) / μ) * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 +
        sourcePair (posGraph (rieszLift w)) (negGraph (rieszLift w)) := by
  set p := rieszLift w
  have hp_fst : p.val.fst = μ • w := heig
  have hpair := sourcePair_rieszLift_of_eigenvector heig (posGraph p)
  have hsub : sourcePair p (posGraph p) =
      sourceEnergy (posGraph p) - sourcePair (negGraph p) (posGraph p) := by
    have h1 := congrArg (fun q : SourceGraph => sourcePair q (posGraph p)) (posGraph_sub_negGraph p).symm
    change sourcePair p (posGraph p) = sourcePair (posGraph p - negGraph p) (posGraph p) at h1
    rw [h1, sourcePair_sub_left, sourcePair_self]
  have hinner : ⟪w, (posGraph p).val.fst⟫_ℝ = (1 / μ) * ‖(posGraph p).val.fst‖ ^ 2 := by
    have h2 : ⟪p.val.fst, (posGraph p).val.fst⟫_ℝ = ‖(posGraph p).val.fst‖ ^ 2 := by
      have h1 := congrArg (fun q : SourceGraph => ⟪q.val.fst, (posGraph p).val.fst⟫_ℝ)
        (posGraph_sub_negGraph p).symm
      change ⟪p.val.fst, (posGraph p).val.fst⟫_ℝ =
        ⟪(posGraph p).val.fst - (negGraph p).val.fst, (posGraph p).val.fst⟫_ℝ at h1
      rw [h1, inner_sub_left, real_inner_self_eq_norm_sq,
        real_inner_comm (posGraph p).val.fst (negGraph p).val.fst,
        inner_posGraph_negGraph_fst, sub_zero]
    rw [hp_fst, real_inner_smul_left] at h2
    rw [← h2]
    field_simp [hμ]
  rw [hsub, sourcePair_symm (negGraph p) (posGraph p), hinner] at hpair
  have hring : (1 - 2 * μ) * (1 / μ * ‖(posGraph p).val.fst‖ ^ 2) =
      (1 - 2 * μ) / μ * ‖(posGraph p).val.fst‖ ^ 2 := by ring
  linarith

/-- **Strict Rayleigh-Quotient Boost for the Positive Part and Absolute Value of Any Primitive Eigenvector.**
For every nonzero primitive eigenvector `w` of `resolvent` with eigenvalue `μ > 0` (and in
particular every nonzero odd eigenvector), both `(posGraph (rieszLift w)).val.fst` and
`(absGraph (rieszLift w)).val.fst` have Rayleigh quotient strictly greater than `μ`. -/
theorem rayleigh_posGraph_and_absGraph_gt_of_primitive_eigenvector {μ : ℝ} (hμ : 0 < μ)
    {w : MassSpace} (hw0 : w ≠ 0) (hprim : ⟪w, oneL⟫_ℝ = 0) (heig : resolvent w = μ • w) :
    μ * ‖(posGraph (rieszLift w)).val.fst‖ ^ 2 <
        ⟪resolvent (posGraph (rieszLift w)).val.fst, (posGraph (rieszLift w)).val.fst⟫_ℝ ∧
      μ * ‖(absGraph (rieszLift w)).val.fst‖ ^ 2 <
        ⟪resolvent (absGraph (rieszLift w)).val.fst, (absGraph (rieszLift w)).val.fst⟫_ℝ := by
  set p := rieszLift w
  have hp_fst : p.val.fst = μ • w := heig
  have hp0 : p ≠ 0 := by
    intro h
    have hf : p.val.fst = 0 := by rw [h]; rfl
    rw [hp_fst, smul_eq_zero] at hf
    exact hw0 (hf.resolve_left hμ.ne')
  have hp_prim : ⟪p.val.fst, oneL⟫_ℝ = 0 := by
    rw [hp_fst, real_inner_smul_left, hprim, mul_zero]
  obtain ⟨hpos_ne, hneg_ne⟩ := posGraph_ne_zero_and_negGraph_ne_zero_of_primitive hp0 hp_prim
  have hpair_neg : sourcePair (posGraph p) (negGraph p) < 0 :=
    sourcePair_posGraph_negGraph_neg_of_ne_zero hpos_ne hneg_ne
  constructor
  · have hpos_fst_ne : (posGraph p).val.fst ≠ 0 :=
      fun h => hpos_ne (source_projection_injective h)
    have hnorm_pos : 0 < ‖(posGraph p).val.fst‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr hpos_fst_ne) 2
    have hE := sourceEnergy_posGraph_rieszLift_of_eigenvector hμ.ne' heig
    have hsum : sourceEnergy (posGraph p) + 2 * ‖(posGraph p).val.fst‖ ^ 2 <
        (1 / μ) * ‖(posGraph p).val.fst‖ ^ 2 := by
      have hid : (1 - 2 * μ) / μ * ‖(posGraph p).val.fst‖ ^ 2 + 2 * ‖(posGraph p).val.fst‖ ^ 2 =
          (1 / μ) * ‖(posGraph p).val.fst‖ ^ 2 := by
        field_simp [hμ.ne']
        ring
      linarith
    have hcs := norm_fst_pow_four_le_inner_resolvent_mul (posGraph p)
    have hRnn : 0 ≤ ⟪resolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ := by
      rw [inner_resolvent_self]; positivity
    have hRpos : 0 < ⟪resolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ := by
      rcases hRnn.eq_or_lt with h0 | hlt
      · exfalso
        rw [← h0, zero_mul] at hcs
        have : 0 < ‖(posGraph p).val.fst‖ ^ 4 := by positivity
        linarith
      · exact hlt
    have hlt_mul : ‖(posGraph p).val.fst‖ ^ 4 <
        ⟪resolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ *
          ((1 / μ) * ‖(posGraph p).val.fst‖ ^ 2) :=
      lt_of_le_of_lt hcs (mul_lt_mul_of_pos_left hsum hRpos)
    have hlt2 : μ * ‖(posGraph p).val.fst‖ ^ 4 <
        ⟪resolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ * ‖(posGraph p).val.fst‖ ^ 2 := by
      have hm := mul_lt_mul_of_pos_left hlt_mul hμ
      have heq : μ * (⟪resolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ *
          (1 / μ * ‖(posGraph p).val.fst‖ ^ 2)) =
          ⟪resolvent (posGraph p).val.fst, (posGraph p).val.fst⟫_ℝ * ‖(posGraph p).val.fst‖ ^ 2 := by
        field_simp [hμ.ne']
      linarith
    have hpow4 : ‖(posGraph p).val.fst‖ ^ 4 =
        ‖(posGraph p).val.fst‖ ^ 2 * ‖(posGraph p).val.fst‖ ^ 2 := by ring
    nlinarith
  · have habs_fst_ne : (absGraph p).val.fst ≠ 0 := by
      intro h
      have hn0 : ‖(absGraph p).val.fst‖ = 0 := by rw [h, norm_zero]
      rw [norm_absGraph_fst, norm_eq_zero] at hn0
      exact hp0 (source_projection_injective hn0)
    have hnorm_pos : 0 < ‖(absGraph p).val.fst‖ ^ 2 :=
      pow_pos (norm_pos_iff.mpr habs_fst_ne) 2
    have hEp : sourceEnergy p = ((1 - 2 * μ) / μ) * ‖p.val.fst‖ ^ 2 := by
      change sourceEnergy (rieszLift w) = _
      rw [sourceEnergy_rieszLift, hp_fst, heig, real_inner_smul_right, norm_smul, Real.norm_eq_abs,
        abs_of_pos hμ, real_inner_self_eq_norm_sq]
      field_simp [hμ.ne']
    have hEabs := sourceEnergy_absGraph_eq p
    rw [hEp, ← norm_absGraph_fst_sq p] at hEabs
    have hsum : sourceEnergy (absGraph p) + 2 * ‖(absGraph p).val.fst‖ ^ 2 <
        (1 / μ) * ‖(absGraph p).val.fst‖ ^ 2 := by
      have hid : (1 - 2 * μ) / μ * ‖(absGraph p).val.fst‖ ^ 2 + 2 * ‖(absGraph p).val.fst‖ ^ 2 =
          (1 / μ) * ‖(absGraph p).val.fst‖ ^ 2 := by
        field_simp [hμ.ne']
        ring
      linarith
    have hcs := norm_fst_pow_four_le_inner_resolvent_mul (absGraph p)
    have hRnn : 0 ≤ ⟪resolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ := by
      rw [inner_resolvent_self]; positivity
    have hRpos : 0 < ⟪resolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ := by
      rcases hRnn.eq_or_lt with h0 | hlt
      · exfalso
        rw [← h0, zero_mul] at hcs
        have : 0 < ‖(absGraph p).val.fst‖ ^ 4 := by positivity
        linarith
      · exact hlt
    have hlt_mul : ‖(absGraph p).val.fst‖ ^ 4 <
        ⟪resolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ *
          ((1 / μ) * ‖(absGraph p).val.fst‖ ^ 2) :=
      lt_of_le_of_lt hcs (mul_lt_mul_of_pos_left hsum hRpos)
    have hlt2 : μ * ‖(absGraph p).val.fst‖ ^ 4 <
        ⟪resolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ * ‖(absGraph p).val.fst‖ ^ 2 := by
      have hm := mul_lt_mul_of_pos_left hlt_mul hμ
      have heq : μ * (⟪resolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ *
          (1 / μ * ‖(absGraph p).val.fst‖ ^ 2)) =
          ⟪resolvent (absGraph p).val.fst, (absGraph p).val.fst⟫_ℝ * ‖(absGraph p).val.fst‖ ^ 2 := by
        field_simp [hμ.ne']
      linarith
    have hpow4 : ‖(absGraph p).val.fst‖ ^ 4 =
        ‖(absGraph p).val.fst‖ ^ 2 * ‖(absGraph p).val.fst‖ ^ 2 := by ring
    nlinarith

/-! ## Section 3: Parity Decomposition of `boundStateSpace` and Sector Dimension Bounds -/

/-- The closed span of all odd bound states of the arithmetic resolvent above `1/2`. -/
def oddBoundStateSpace : Submodule ℝ MassSpace :=
  (Submodule.span ℝ {w : MassSpace | ∃ μ : ℝ, 1 / 2 < μ ∧ reflectMass w = -w ∧ resolvent w = μ • w}).topologicalClosure

/-- The closed span of all even bound states of the arithmetic resolvent above `1/2`. -/
def evenBoundStateSpace : Submodule ℝ MassSpace :=
  (Submodule.span ℝ {w : MassSpace | ∃ μ : ℝ, 1 / 2 < μ ∧ reflectMass w = w ∧ resolvent w = μ • w}).topologicalClosure

theorem isClosed_oddBoundStateSpace : IsClosed (oddBoundStateSpace : Set MassSpace) :=
  Submodule.isClosed_topologicalClosure _

theorem isClosed_evenBoundStateSpace : IsClosed (evenBoundStateSpace : Set MassSpace) :=
  Submodule.isClosed_topologicalClosure _

theorem mem_oddBoundStateSpace_of_eigen {μ : ℝ} (hμ : 1 / 2 < μ) {w : MassSpace}
    (hodd : reflectMass w = -w) (heig : resolvent w = μ • w) : w ∈ oddBoundStateSpace :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, hμ, hodd, heig⟩)

theorem mem_evenBoundStateSpace_of_eigen {μ : ℝ} (hμ : 1 / 2 < μ) {w : MassSpace}
    (heven : reflectMass w = w) (heig : resolvent w = μ • w) : w ∈ evenBoundStateSpace :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨μ, hμ, heven, heig⟩)

theorem oneL_mem_evenBoundStateSpace : oneL ∈ evenBoundStateSpace :=
  mem_evenBoundStateSpace_of_eigen (μ := 1) (by norm_num) reflectMass_oneL
    (by rw [resolvent_oneL, one_smul])

theorem oddBoundStateSpace_le_oddSector : oddBoundStateSpace ≤ oddSector := by
  refine Submodule.topologicalClosure_minimal _ ?_ isClosed_oddSector
  rw [Submodule.span_le]
  rintro w ⟨_, _, hodd, _⟩
  exact mem_oddSector.mpr hodd

theorem evenBoundStateSpace_le_evenSector : evenBoundStateSpace ≤ evenSector := by
  refine Submodule.topologicalClosure_minimal _ ?_ isClosed_evenSector
  rw [Submodule.span_le]
  rintro w ⟨_, _, heven, _⟩
  exact mem_evenSector.mpr heven

theorem oddBoundStateSpace_le_boundStateSpace : oddBoundStateSpace ≤ boundStateSpace := by
  refine Submodule.topologicalClosure_minimal _ ?_ isClosed_boundStateSpace
  rw [Submodule.span_le]
  rintro w ⟨μ, hμ, _, heig⟩
  exact mem_boundStateSpace_of_eigen hμ heig

theorem evenBoundStateSpace_le_boundStateSpace : evenBoundStateSpace ≤ boundStateSpace := by
  refine Submodule.topologicalClosure_minimal _ ?_ isClosed_boundStateSpace
  rw [Submodule.span_le]
  rintro w ⟨μ, hμ, _, heig⟩
  exact mem_boundStateSpace_of_eigen hμ heig

/-- The continuous even projection `w ↦ ½ (w + J w)`. -/
def evenProj : MassSpace →L[ℝ] MassSpace :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ MassSpace + reflectMass.toContinuousLinearMap)

/-- The continuous odd projection `w ↦ ½ (w - J w)`. -/
def oddProj : MassSpace →L[ℝ] MassSpace :=
  (1 / 2 : ℝ) • (ContinuousLinearMap.id ℝ MassSpace - reflectMass.toContinuousLinearMap)

theorem evenProj_apply (w : MassSpace) :
    evenProj w = (1 / 2 : ℝ) • (w + reflectMass w) := rfl

theorem oddProj_apply (w : MassSpace) :
    oddProj w = (1 / 2 : ℝ) • (w - reflectMass w) := rfl

theorem evenProj_add_oddProj (w : MassSpace) : evenProj w + oddProj w = w := by
  rw [evenProj_apply, oddProj_apply, ← smul_add, add_add_sub_cancel, ← two_smul ℝ w, smul_smul]
  norm_num

theorem evenProj_eq_self_of_even {w : MassSpace} (hw : w ∈ evenSector) : evenProj w = w := by
  rw [evenProj_apply, mem_evenSector.mp hw, ← two_smul ℝ w, smul_smul]
  norm_num

theorem oddProj_eq_self_of_odd {w : MassSpace} (hw : w ∈ oddSector) : oddProj w = w := by
  rw [oddProj_apply, mem_oddSector.mp hw, sub_neg_eq_add, ← two_smul ℝ w, smul_smul]
  norm_num

theorem evenProj_mem_evenBoundStateSpace {w : MassSpace} (hw : w ∈ boundStateSpace) :
    evenProj w ∈ evenBoundStateSpace := by
  have hspan : Submodule.span ℝ {u : MassSpace | ∃ μ : ℝ, 1 / 2 < μ ∧ resolvent u = μ • u} ≤
      evenBoundStateSpace.comap (evenProj : MassSpace →ₗ[ℝ] MassSpace) := by
    rw [Submodule.span_le]
    rintro u ⟨μ, hμ, heig⟩
    show evenProj u ∈ evenBoundStateSpace
    obtain ⟨heven, heig'⟩ := evenPart_eigenvector heig
    exact mem_evenBoundStateSpace_of_eigen hμ heven heig'
  have hclosed : IsClosed ((evenBoundStateSpace.comap (evenProj : MassSpace →ₗ[ℝ] MassSpace) :
      Submodule ℝ MassSpace) : Set MassSpace) :=
    isClosed_evenBoundStateSpace.preimage evenProj.continuous
  exact Submodule.topologicalClosure_minimal _ hspan hclosed hw

theorem oddProj_mem_oddBoundStateSpace {w : MassSpace} (hwB : w ∈ boundStateSpace) :
    oddProj w ∈ oddBoundStateSpace := by
  have hspan : Submodule.span ℝ {u : MassSpace | ∃ μ : ℝ, 1 / 2 < μ ∧ resolvent u = μ • u} ≤
      oddBoundStateSpace.comap (oddProj : MassSpace →ₗ[ℝ] MassSpace) := by
    rw [Submodule.span_le]
    rintro u ⟨μ, hμ, heig⟩
    show oddProj u ∈ oddBoundStateSpace
    obtain ⟨hodd, heig'⟩ := oddPart_eigenvector heig
    exact mem_oddBoundStateSpace_of_eigen hμ hodd heig'
  have hclosed : IsClosed ((oddBoundStateSpace.comap (oddProj : MassSpace →ₗ[ℝ] MassSpace) :
      Submodule ℝ MassSpace) : Set MassSpace) :=
    isClosed_oddBoundStateSpace.preimage oddProj.continuous
  exact Submodule.topologicalClosure_minimal _ hspan hclosed hwB

/-- **Unconditional identification of `evenBoundStateSpace` as `boundStateSpace ⊓ evenSector`.** -/
theorem evenBoundStateSpace_eq_inf :
    evenBoundStateSpace = boundStateSpace ⊓ evenSector := by
  refine le_antisymm (le_inf evenBoundStateSpace_le_boundStateSpace evenBoundStateSpace_le_evenSector) ?_
  rintro w ⟨hwB, hwE⟩
  rw [← evenProj_eq_self_of_even hwE]
  exact evenProj_mem_evenBoundStateSpace hwB

/-- **Unconditional identification of `oddBoundStateSpace` as `boundStateSpace ⊓ oddSector`.** -/
theorem oddBoundStateSpace_eq_inf :
    oddBoundStateSpace = boundStateSpace ⊓ oddSector := by
  refine le_antisymm (le_inf oddBoundStateSpace_le_boundStateSpace oddBoundStateSpace_le_oddSector) ?_
  rintro w ⟨hwB, hwO⟩
  rw [← oddProj_eq_self_of_odd hwO]
  exact oddProj_mem_oddBoundStateSpace hwB

/-- **Unconditional Parity Decomposition of `boundStateSpace`.** -/
theorem boundStateSpace_eq_sup_even_odd :
    boundStateSpace = evenBoundStateSpace ⊔ oddBoundStateSpace := by
  refine le_antisymm ?_ (sup_le evenBoundStateSpace_le_boundStateSpace oddBoundStateSpace_le_boundStateSpace)
  intro w hw
  rw [← evenProj_add_oddProj w]
  exact Submodule.add_mem_sup (evenProj_mem_evenBoundStateSpace hw)
    (oddProj_mem_oddBoundStateSpace hw)

theorem disjoint_evenSector_oddSector : Disjoint evenSector oddSector := by
  rw [Submodule.disjoint_def]
  intro w hwE hwO
  have h1 := mem_evenSector.mp hwE
  have h2 := mem_oddSector.mp hwO
  rw [h1] at h2
  have h3 : (2 : ℝ) • w = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr h2
  exact (smul_eq_zero.mp h3).resolve_left two_ne_zero

theorem disjoint_evenBoundStateSpace_oddBoundStateSpace :
    Disjoint evenBoundStateSpace oddBoundStateSpace :=
  disjoint_evenSector_oddSector.mono evenBoundStateSpace_le_evenSector oddBoundStateSpace_le_oddSector

/-- **Dimension of a span of odd bound states above `1/2` is at most `#(quarterZeros)`.** -/
theorem finrank_span_odd_eigen_le (hfin : offLineZeros.Finite) {ι : Type*} [Fintype ι]
    (e : ι → MassSpace) (μ : ι → ℝ) (hμ : ∀ i, 1 / 2 < μ i)
    (hodd : ∀ i, reflectMass (e i) = -e i)
    (heig : ∀ i, resolvent (e i) = μ i • e i) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) ≤ quarterZeros.ncard := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Set.range_eq_empty, Submodule.span_empty, finrank_bot]
    omega
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ μ Finset.univ_nonempty
  set a := μ i₀ with ha_def
  have ha : 1 / 2 < a := hμ i₀
  have hamin : ∀ i, a ≤ μ i := fun i => hi₀ i (Finset.mem_univ i)
  set U : Submodule ℝ MassSpace := Submodule.span ℝ (Set.range e) with hU
  haveI : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  have hU_odd : U ≤ oddSector := by
    rw [Submodule.span_le]
    rintro w ⟨i, rfl⟩
    exact mem_oddSector.mpr (hodd i)
  let b := stdOrthonormalBasis ℝ U
  let f : Fin (Module.finrank ℝ U) → MassSpace := fun i => ((b i : U) : MassSpace)
  have hf : Orthonormal ℝ f := by
    refine orthonormal_iff_ite.mpr fun i j => ?_
    exact orthonormal_iff_ite.mp b.orthonormal i j
  have hfU : ∀ i, f i ∈ U := fun i => (b i).2
  have hf_odd : ∀ i, reflectGraph (rieszLift (f i)) = -rieszLift (f i) := fun i =>
    reflectGraph_eq_neg_of_odd (resolventInvariant_oddSector (f i) (hU_odd (hfU i)))
  have hneg : ∀ c : Fin (Module.finrank ℝ U) → ℝ,
      weilForm (∑ i, c i • rieszLift (f i)) ≤ -(a * (2 * a - 1)) * ∑ i, c i ^ 2 := by
    intro c
    rw [← rieszLift_sum]
    set u := ∑ i, c i • f i with hu_def
    have huU : u ∈ U := Submodule.sum_mem _ fun i _ => U.smul_mem _ (hfU i)
    have huprim : ⟪u, oneL⟫_ℝ = 0 := inner_oneL_eq_zero_of_odd (hU_odd huU)
    have hnorm : ‖u‖ ^ 2 = ∑ i, c i ^ 2 := by
      rw [← real_inner_self_eq_norm_sq, hu_def, hf.inner_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [conj_trivial, sq]
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp huU
    have hlow : a * ‖u‖ ^ 2 ≤ ⟪resolvent u, u⟫_ℝ := by
      rw [← hd]
      exact inner_resolvent_sum_ge e μ heig hamin d
    have hE := sourceEnergy_rieszLift_le_of_lower_bound ha hlow
    have hW : weilForm (rieszLift u) ≤ sourceEnergy (rieszLift u) := by
      apply weilForm_le_sourceEnergy_of_primitive
      show ⟪resolvent u, oneL⟫_ℝ = 0
      rw [inner_resolvent_oneL, real_inner_comm, huprim]
    rw [hnorm] at hE
    linarith
  have hδ : 0 < a * (2 * a - 1) := mul_pos (by linarith) (by linarith)
  obtain ⟨q, hq, hq_c, hq_odd, hqneg⟩ :=
    exists_odd_compactTests_negative_definite (fun i => rieszLift (f i)) hf_odd hδ hneg
  exact card_le_quarter_of_odd_negative_definite hfin q hq hq_c hq_odd hqneg

/-- **Dimension of a span of even bound states above `1/2` is at most `#(quarterZeros) + 1`.** -/
theorem finrank_span_even_eigen_le (hfin : offLineZeros.Finite) {ι : Type*} [Fintype ι]
    (e : ι → MassSpace) (μ : ι → ℝ) (hμ : ∀ i, 1 / 2 < μ i)
    (heven : ∀ i, reflectMass (e i) = e i)
    (heig : ∀ i, resolvent (e i) = μ i • e i) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range e)) ≤ quarterZeros.ncard + 1 := by
  classical
  rcases isEmpty_or_nonempty ι with hι | hι
  · rw [Set.range_eq_empty, Submodule.span_empty, finrank_bot]
    omega
  obtain ⟨i₀, _, hi₀⟩ := Finset.exists_min_image Finset.univ μ Finset.univ_nonempty
  set a := μ i₀ with ha_def
  have ha : 1 / 2 < a := hμ i₀
  have hamin : ∀ i, a ≤ μ i := fun i => hi₀ i (Finset.mem_univ i)
  set U : Submodule ℝ MassSpace := Submodule.span ℝ (Set.range e) with hU
  haveI : FiniteDimensional ℝ U := FiniteDimensional.span_of_finite ℝ (Set.finite_range e)
  have hU_even : U ≤ evenSector := by
    rw [Submodule.span_le]
    rintro w ⟨i, rfl⟩
    exact mem_evenSector.mpr (heven i)
  let ℓ : U →ₗ[ℝ] ℝ :=
    { toFun := fun u => ⟪(u : MassSpace), oneL⟫_ℝ
      map_add' := fun u v => by simp [inner_add_left]
      map_smul' := fun r u => by simp [real_inner_smul_left] }
  have hrange : Module.finrank ℝ (LinearMap.range ℓ) ≤ 1 := by
    calc Module.finrank ℝ (LinearMap.range ℓ) ≤ Module.finrank ℝ ℝ := Submodule.finrank_le _
      _ = 1 := Module.finrank_self ℝ
  have hker : Module.finrank ℝ (LinearMap.ker ℓ) ≤ quarterZeros.ncard := by
    set K := LinearMap.ker ℓ with hK
    let b := stdOrthonormalBasis ℝ K
    let f : Fin (Module.finrank ℝ K) → MassSpace := fun i => ((b i : U) : MassSpace)
    have hf : Orthonormal ℝ f := by
      refine orthonormal_iff_ite.mpr fun i j => ?_
      exact orthonormal_iff_ite.mp b.orthonormal i j
    have hfU : ∀ i, f i ∈ U := fun i => (b i).1.2
    have hf_even : ∀ i, reflectGraph (rieszLift (f i)) = rieszLift (f i) := fun i =>
      reflectGraph_eq_self_of_even (mem_evenSector.mp (resolventInvariant_evenSector (f i) (hU_even (hfU i))))
    have hfprim : ∀ i, ⟪f i, oneL⟫_ℝ = 0 := fun i => LinearMap.mem_ker.mp (b i).2
    have hneg : ∀ c : Fin (Module.finrank ℝ K) → ℝ,
        weilForm (∑ i, c i • rieszLift (f i)) ≤ -(a * (2 * a - 1)) * ∑ i, c i ^ 2 := by
      intro c
      rw [← rieszLift_sum]
      set u := ∑ i, c i • f i with hu_def
      have huU : u ∈ U := Submodule.sum_mem _ fun i _ => U.smul_mem _ (hfU i)
      have huprim : ⟪u, oneL⟫_ℝ = 0 := by
        rw [hu_def, sum_inner]
        exact Finset.sum_eq_zero fun i _ => by rw [real_inner_smul_left, hfprim i, mul_zero]
      have hnorm : ‖u‖ ^ 2 = ∑ i, c i ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, hu_def, hf.inner_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [conj_trivial, sq]
      obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp huU
      have hlow : a * ‖u‖ ^ 2 ≤ ⟪resolvent u, u⟫_ℝ := by
        rw [← hd]
        exact inner_resolvent_sum_ge e μ heig hamin d
      have hE := sourceEnergy_rieszLift_le_of_lower_bound ha hlow
      have hW : weilForm (rieszLift u) ≤ sourceEnergy (rieszLift u) := by
        apply weilForm_le_sourceEnergy_of_primitive
        show ⟪resolvent u, oneL⟫_ℝ = 0
        rw [inner_resolvent_oneL, real_inner_comm, huprim]
      rw [hnorm] at hE
      linarith
    have hδ : 0 < a * (2 * a - 1) := mul_pos (by linarith) (by linarith)
    obtain ⟨q, hq, hq_c, hq_even, hqneg⟩ :=
      exists_even_compactTests_negative_definite (fun i => rieszLift (f i)) hf_even hδ hneg
    exact card_le_quarter_of_even_negative_definite hfin q hq hq_c hq_even hqneg
  have h := LinearMap.finrank_range_add_finrank_ker ℓ
  omega

theorem oddBoundStateSpace_eq_span_of_finite (hfin : offLineZeros.Finite) :
    ∃ b : Set MassSpace, b.Finite ∧ b.ncard ≤ quarterZeros.ncard ∧
      oddBoundStateSpace = Submodule.span ℝ b := by
  classical
  set S : Set MassSpace :=
    {w | ∃ μ : ℝ, 1 / 2 < μ ∧ reflectMass w = -w ∧ resolvent w = μ • w} with hS
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ S
  have hcard : ∀ t : Finset MassSpace, (↑t : Set MassSpace) ⊆ b →
      t.card ≤ quarterZeros.ncard := by
    intro t htb
    let e : t → MassSpace := fun x => (x : MassSpace)
    have hinj : Function.Injective fun x : t => (⟨x.1, htb x.2⟩ : b) :=
      fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h)
    have hli' : LinearIndependent ℝ e := hli.comp (fun x : t => (⟨x.1, htb x.2⟩ : b)) hinj
    have he : ∀ x : t, ∃ μ : ℝ, 1 / 2 < μ ∧ reflectMass (e x) = -e x ∧
        resolvent (e x) = μ • e x := fun x => hbS (htb x.2)
    choose μ hμ hodd heig using he
    have := finrank_span_odd_eigen_le hfin e μ hμ hodd heig
    rwa [finrank_span_eq_card hli', Fintype.card_coe] at this
  have hbfin : b.Finite := by
    by_contra hinf
    obtain ⟨t, htb, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (quarterZeros.ncard + 1)
    have := hcard t htb
    omega
  refine ⟨b, hbfin, ?_, ?_⟩
  · rw [Set.ncard_eq_toFinset_card b hbfin]
    exact hcard _ hbfin.coe_toFinset.subset
  · haveI : FiniteDimensional ℝ (Submodule.span ℝ b) := FiniteDimensional.span_of_finite ℝ hbfin
    unfold oddBoundStateSpace
    rw [← hspan]
    exact IsClosed.submodule_topologicalClosure_eq (Submodule.closed_of_finiteDimensional _)

theorem evenBoundStateSpace_eq_span_of_finite (hfin : offLineZeros.Finite) :
    ∃ b : Set MassSpace, b.Finite ∧ b.ncard ≤ quarterZeros.ncard + 1 ∧
      evenBoundStateSpace = Submodule.span ℝ b := by
  classical
  set S : Set MassSpace :=
    {w | ∃ μ : ℝ, 1 / 2 < μ ∧ reflectMass w = w ∧ resolvent w = μ • w} with hS
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℝ S
  have hcard : ∀ t : Finset MassSpace, (↑t : Set MassSpace) ⊆ b →
      t.card ≤ quarterZeros.ncard + 1 := by
    intro t htb
    let e : t → MassSpace := fun x => (x : MassSpace)
    have hinj : Function.Injective fun x : t => (⟨x.1, htb x.2⟩ : b) :=
      fun x y h => Subtype.ext (by simpa using congrArg Subtype.val h)
    have hli' : LinearIndependent ℝ e := hli.comp (fun x : t => (⟨x.1, htb x.2⟩ : b)) hinj
    have he : ∀ x : t, ∃ μ : ℝ, 1 / 2 < μ ∧ reflectMass (e x) = e x ∧
        resolvent (e x) = μ • e x := fun x => hbS (htb x.2)
    choose μ hμ heven heig using he
    have := finrank_span_even_eigen_le hfin e μ hμ heven heig
    rwa [finrank_span_eq_card hli', Fintype.card_coe] at this
  have hbfin : b.Finite := by
    by_contra hinf
    obtain ⟨t, htb, htc⟩ := Set.Infinite.exists_subset_card_eq hinf (quarterZeros.ncard + 2)
    have := hcard t htb
    omega
  refine ⟨b, hbfin, ?_, ?_⟩
  · rw [Set.ncard_eq_toFinset_card b hbfin]
    exact hcard _ hbfin.coe_toFinset.subset
  · haveI : FiniteDimensional ℝ (Submodule.span ℝ b) := FiniteDimensional.span_of_finite ℝ hbfin
    unfold evenBoundStateSpace
    rw [← hspan]
    exact IsClosed.submodule_topologicalClosure_eq (Submodule.closed_of_finiteDimensional _)

theorem finiteDimensional_oddBoundStateSpace (hfin : offLineZeros.Finite) :
    FiniteDimensional ℝ oddBoundStateSpace := by
  obtain ⟨b, hbfin, -, hb⟩ := oddBoundStateSpace_eq_span_of_finite hfin
  rw [hb]
  exact FiniteDimensional.span_of_finite ℝ hbfin

theorem finrank_oddBoundStateSpace_le (hfin : offLineZeros.Finite) :
    Module.finrank ℝ oddBoundStateSpace ≤ quarterZeros.ncard := by
  classical
  obtain ⟨b, hbfin, hcard, hb⟩ := oddBoundStateSpace_eq_span_of_finite hfin
  rw [hb]
  haveI := hbfin.fintype
  refine (finrank_span_le_card b).trans ?_
  rw [← hbfin.toFinset_eq_toFinset, ← Set.ncard_eq_toFinset_card b hbfin]
  exact hcard

theorem finiteDimensional_evenBoundStateSpace (hfin : offLineZeros.Finite) :
    FiniteDimensional ℝ evenBoundStateSpace := by
  obtain ⟨b, hbfin, -, hb⟩ := evenBoundStateSpace_eq_span_of_finite hfin
  rw [hb]
  exact FiniteDimensional.span_of_finite ℝ hbfin

theorem finrank_evenBoundStateSpace_le (hfin : offLineZeros.Finite) :
    Module.finrank ℝ evenBoundStateSpace ≤ quarterZeros.ncard + 1 := by
  classical
  obtain ⟨b, hbfin, hcard, hb⟩ := evenBoundStateSpace_eq_span_of_finite hfin
  rw [hb]
  haveI := hbfin.fintype
  refine (finrank_span_le_card b).trans ?_
  rw [← hbfin.toFinset_eq_toFinset, ← Set.ncard_eq_toFinset_card b hbfin]
  exact hcard

/-- **Exact Parity Dimension Split of `boundStateSpace`.** -/
theorem finrank_boundStateSpace_eq_add_parity (hfin : offLineZeros.Finite) :
    Module.finrank ℝ boundStateSpace =
      Module.finrank ℝ evenBoundStateSpace + Module.finrank ℝ oddBoundStateSpace := by
  haveI := finiteDimensional_evenBoundStateSpace hfin
  haveI := finiteDimensional_oddBoundStateSpace hfin
  rw [boundStateSpace_eq_sup_even_odd]
  have h := Submodule.finrank_sup_add_finrank_inf_eq evenBoundStateSpace oddBoundStateSpace
  rw [disjoint_evenBoundStateSpace_oddBoundStateSpace.eq_bot, finrank_bot, add_zero] at h
  exact h

/-- **RH ⟺ `oddBoundStateSpace = ⊥`.** -/
theorem riemannHypothesis_iff_oddBoundStateSpace_eq_bot :
    RiemannHypothesis ↔ oddBoundStateSpace = ⊥ := by
  rw [riemannHypothesis_iff_no_odd_bound_state]
  constructor
  · intro h
    rw [eq_bot_iff]
    refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.closed_of_finiteDimensional _)
    rw [Submodule.span_le]
    rintro w ⟨μ, hμ, hodd, heig⟩
    exact (Submodule.mem_bot ℝ).mpr (h μ w hμ hodd heig)
  · intro h μ w hμ hodd heig
    have hw : w ∈ (⊥ : Submodule ℝ MassSpace) := by
      rw [← h]
      exact mem_oddBoundStateSpace_of_eigen hμ hodd heig
    exact (Submodule.mem_bot ℝ).mp hw

/-- **RH ⟺ `evenBoundStateSpace = ℝ ∙ oneL`.** -/
theorem riemannHypothesis_iff_evenBoundStateSpace_eq_span_oneL :
    RiemannHypothesis ↔ evenBoundStateSpace = ℝ ∙ oneL := by
  constructor
  · intro hRH
    have hB := riemannHypothesis_iff_boundStateSpace_eq_span_oneL.mp hRH
    refine le_antisymm ?_ ?_
    · exact evenBoundStateSpace_le_boundStateSpace.trans hB.le
    · rw [Submodule.span_singleton_le_iff_mem]
      exact oneL_mem_evenBoundStateSpace
  · intro h
    rw [riemannHypothesis_iff_no_evenPrimitive_bound_state]
    intro μ w hμ heven hprim heig
    have hw : w ∈ ℝ ∙ oneL := by
      rw [← h]
      exact mem_evenBoundStateSpace_of_eigen hμ heven heig
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hw
    rw [real_inner_smul_left, real_inner_self_eq_norm_sq, norm_oneL_sq] at hprim
    have ha : a = 0 := by linarith
    rw [ha, zero_smul]

/-- **RH ⟺ `Module.finrank ℝ evenBoundStateSpace = 1`.** -/
theorem riemannHypothesis_iff_finrank_evenBoundStateSpace_eq_one :
    RiemannHypothesis ↔ Module.finrank ℝ evenBoundStateSpace = 1 := by
  rw [riemannHypothesis_iff_evenBoundStateSpace_eq_span_oneL]
  constructor
  · intro h
    rw [h]
    exact finrank_span_singleton oneL_ne_zero
  · intro h
    haveI : FiniteDimensional ℝ evenBoundStateSpace := Module.finite_of_finrank_pos (by omega)
    symm
    refine Submodule.eq_of_le_of_finrank_eq ?_ ?_
    · rw [Submodule.span_singleton_le_iff_mem]
      exact oneL_mem_evenBoundStateSpace
    · rw [h, finrank_span_singleton oneL_ne_zero]

end RHTower.CHMDPolar
