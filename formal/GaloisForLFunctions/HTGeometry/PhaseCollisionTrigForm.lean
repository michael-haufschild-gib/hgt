/-
# The phase collision as a low-frequency trigonometric polynomial

The collision of the uniform phase seed against an orthonormal family is a quartic in the phases,
so expanding it gives a character sum indexed by four register points, whose frequency vector is
supported on at most four coordinates with entries in `[-2,2]`.  Squaring gives eight points with
entries in `[-4,4]`.  This is the shape the eighth-root transfer consumes.

Main results:
* `collisionFreq`, `collisionCoeff` — the quartic index data.
* `phaseCollision_eq_trigLift` — **the collision is a trigonometric polynomial**.
* `card_freqSupport_collisionFreq_le` — its frequencies occupy at most four coordinates.
* `collisionFreq_abs_le` — with entries at most two in absolute value.
-/
import GaloisForLFunctions.HTGeometry.PhaseSeedCollisionMoments
import GaloisForLFunctions.HTGeometry.TorusTrigPoincare

open Finset ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.HTGeometry

set_option linter.unusedSectionVars false

variable {α : Type*} [Fintype α] [DecidableEq α]
variable {ι : Type*} [Fintype ι]

/-- The frequency vector of one quartic register term. -/
def collisionFreq (q : Fin 4 → α) : α → ℤ :=
  fun t => (if t = q 1 then 1 else 0) + (if t = q 3 then 1 else 0)
    - (if t = q 0 then 1 else 0) - (if t = q 2 then 1 else 0)

theorem collisionFreq_eq_sum (q : Fin 4 → α) :
    collisionFreq q = Pi.single (q 1) 1 + Pi.single (q 3) 1
      - Pi.single (q 0) 1 - Pi.single (q 2) 1 := by
  funext t
  simp [collisionFreq, Pi.single_apply]

theorem collisionFreq_abs_le (q : Fin 4 → α) (t : α) : |collisionFreq q t| ≤ 2 := by
  simp only [collisionFreq]
  split_ifs <;> norm_num

theorem collisionFreq_support_subset (q : Fin 4 → α) :
    (univ.filter fun t => collisionFreq q t ≠ 0) ⊆ ({q 0, q 1, q 2, q 3} : Finset α) := by
  intro t ht
  rw [Finset.mem_filter] at ht
  by_contra hcon
  refine ht.2 ?_
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hcon
  simp [collisionFreq, hcon.1, hcon.2.1, hcon.2.2.1, hcon.2.2.2]

theorem card_freqSupport_collisionFreq_le (q : Fin 4 → α) :
    (univ.filter fun t => collisionFreq q t ≠ 0).card ≤ 4 := by
  refine le_trans (Finset.card_le_card (collisionFreq_support_subset q)) ?_
  refine le_trans (Finset.card_insert_le _ _) ?_
  have h1 : ({q 1, q 2, q 3} : Finset α).card ≤ 3 := by
    refine le_trans (Finset.card_insert_le _ _) ?_
    have h2 : ({q 2, q 3} : Finset α).card ≤ 2 := by
      refine le_trans (Finset.card_insert_le _ _) ?_
      simp
    omega
  omega

/-- The coefficient of one quartic register term. -/
def collisionCoeff (e : ι → α → ℂ) (q : Fin 4 → α) : ℂ :=
  ((Fintype.card α : ℂ))⁻¹ ^ 2 *
    ∑ j, e j (q 0) * conj (e j (q 1)) * e j (q 2) * conj (e j (q 3))

/-! ## The expansion -/

theorem finiteComplexInner_uniformPhaseSeed (e : ι → α → ℂ) (x : α → ℝ) (j : ι) :
    finiteComplexInner (uniformPhaseSeed x) (e j)
      = ((Real.sqrt ((Fintype.card α : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ a, charLift (-(Pi.single a 1)) x * e j a := by
  rw [finiteComplexInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  show (starRingEnd ℂ) (uniformPhaseSeed x a) * e j a = _
  rw [uniformPhaseSeed, torusReplicaPhaseOrbit, uniformPhaseWeights, map_mul,
    Complex.conj_ofReal, charLift_neg_index]
  ring

theorem conj_finiteComplexInner_uniformPhaseSeed (e : ι → α → ℂ) (x : α → ℝ) (j : ι) :
    (starRingEnd ℂ) (finiteComplexInner (uniformPhaseSeed x) (e j))
      = ((Real.sqrt ((Fintype.card α : ℝ))⁻¹ : ℝ) : ℂ) *
        ∑ b, charLift (Pi.single b 1) x * (starRingEnd ℂ) (e j b) := by
  rw [finiteComplexInner_uniformPhaseSeed, map_mul, Complex.conj_ofReal, map_sum]
  congr 1
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, ← charLift_neg_index, neg_neg]

theorem sqrt_inv_pow_four (D : ℕ) :
    ((Real.sqrt ((D : ℝ))⁻¹ : ℝ) : ℂ) ^ 4 = ((D : ℂ))⁻¹ ^ 2 := by
  have hnn : (0 : ℝ) ≤ ((D : ℝ))⁻¹ := by positivity
  have h : (Real.sqrt ((D : ℝ))⁻¹) ^ 4 = (((D : ℝ))⁻¹) ^ 2 := by
    have h2 : (Real.sqrt ((D : ℝ))⁻¹) ^ 2 = ((D : ℝ))⁻¹ := Real.sq_sqrt hnn
    calc (Real.sqrt ((D : ℝ))⁻¹) ^ 4 = ((Real.sqrt ((D : ℝ))⁻¹) ^ 2) ^ 2 := by ring
      _ = (((D : ℝ))⁻¹) ^ 2 := by rw [h2]
  rw [← Complex.ofReal_pow, h]
  push_cast
  ring

/-- **The collision is a trigonometric polynomial** indexed by four register points. -/
theorem phaseCollision_eq_trigLift (e : ι → α → ℂ) (x : α → ℝ) :
    ((phaseCollision e x : ℝ) : ℂ)
      = trigLift (Finset.univ : Finset (Fin 4 → α)) collisionFreq (collisionCoeff e) x := by
  classical
  obtain ⟨s, hsdef⟩ : ∃ s : ℂ, s = ((Real.sqrt ((Fintype.card α : ℝ))⁻¹ : ℝ) : ℂ) := ⟨_, rfl⟩
  obtain ⟨f, hfdef⟩ : ∃ f : ι → α → ℂ,
      f = fun j a => charLift (-(Pi.single a 1)) x * e j a := ⟨_, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : ι → α → ℂ,
      g = fun j b => charLift (Pi.single b 1) x * (starRingEnd ℂ) (e j b) := ⟨_, rfl⟩
  have hterm : ∀ j : ι, ((finitePureStateFidelity (uniformPhaseSeed x) (e j) ^ 2 : ℝ) : ℂ)
      = s ^ 4 * ∑ q : Fin 4 → α, f j (q 0) * g j (q 1) * f j (q 2) * g j (q 3) := by
    intro j
    obtain ⟨z, hzdef⟩ : ∃ z, z = finiteComplexInner (uniformPhaseSeed x) (e j) := ⟨_, rfl⟩
    have hz2 : ((finitePureStateFidelity (uniformPhaseSeed x) (e j) : ℝ) : ℂ)
        = (starRingEnd ℂ) z * z := by
      rw [finitePureStateFidelity, Complex.sq_norm, ← hzdef]
      exact Complex.normSq_eq_conj_mul_self
    have hz4 : ((finitePureStateFidelity (uniformPhaseSeed x) (e j) ^ 2 : ℝ) : ℂ)
        = ((starRingEnd ℂ) z * z) ^ 2 := by
      rw [Complex.ofReal_pow, hz2]
    rw [hz4]
    have hzf : z = s * ∑ a, f j a := by
      rw [hzdef, hsdef, hfdef]
      exact finiteComplexInner_uniformPhaseSeed e x j
    have hzg : (starRingEnd ℂ) z = s * ∑ b, g j b := by
      rw [hzdef, hsdef, hgdef]
      exact conj_finiteComplexInner_uniformPhaseSeed e x j
    have hprod : (∑ a, f j a) * (∑ b, g j b) * (∑ a, f j a) * (∑ b, g j b)
        = ∑ q : Fin 4 → α, f j (q 0) * g j (q 1) * f j (q 2) * g j (q 3) := by
      have hF := Finset.prod_univ_sum (fun _ : Fin 4 => (Finset.univ : Finset α))
        (fun i : Fin 4 => ![f j, g j, f j, g j] i)
      rw [Fintype.piFinset_univ] at hF
      rw [Fin.prod_univ_four] at hF
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at hF
      rw [show (![f j, g j, f j, g j] (2 : Fin 4)) = f j from rfl,
        show (![f j, g j, f j, g j] (3 : Fin 4)) = g j from rfl] at hF
      rw [hF]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [Fin.prod_univ_four]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
      rw [show (![f j, g j, f j, g j] (2 : Fin 4)) = f j from rfl,
        show (![f j, g j, f j, g j] (3 : Fin 4)) = g j from rfl]
    rw [hzg, hzf, ← hprod]
    ring
  have hcast : ((phaseCollision e x : ℝ) : ℂ)
      = ∑ j, ((finitePureStateFidelity (uniformPhaseSeed x) (e j) ^ 2 : ℝ) : ℂ) := by
    rw [phaseCollision, Complex.ofReal_sum]
  have hAq : ∀ (j : ι) (q : Fin 4 → α), f j (q 0) * g j (q 1) * f j (q 2) * g j (q 3)
      = (e j (q 0) * (starRingEnd ℂ) (e j (q 1)) * e j (q 2) * (starRingEnd ℂ) (e j (q 3)))
        * charLift (collisionFreq q) x := by
    intro j q
    have hchar : charLift (-(Pi.single (q 0) 1)) x * charLift (Pi.single (q 1) 1) x
        * charLift (-(Pi.single (q 2) 1)) x * charLift (Pi.single (q 3) 1) x
        = charLift (collisionFreq q) x := by
      rw [← charLift_add_index, ← charLift_add_index, ← charLift_add_index,
        collisionFreq_eq_sum]
      congr 1
      abel
    rw [hfdef, hgdef, ← hchar]
    ring
  rw [hcast, Finset.sum_congr rfl (fun j _ => hterm j), trigLift, ← Finset.mul_sum,
    Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  conv_rhs => rw [collisionCoeff, ← sqrt_inv_pow_four (Fintype.card α), ← hsdef,
    Finset.mul_sum, Finset.sum_mul]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hAq j q]
  ring

/-! ## Frequencies stay nonzero modulo eight -/

theorem intCast_zmod_eight_ne_zero_of_abs_le {m : ℤ} (hm : m ≠ 0) (hle : |m| ≤ 7) :
    ((m : ℤ) : ZMod 8) ≠ 0 := by
  intro h
  have hdvd := (ZMod.intCast_zmod_eq_zero_iff_dvd m 8).mp h
  have habs : ((8 : ℕ) : ℤ) ∣ |m| := (dvd_abs _ _).mpr hdvd
  have hpos : (0 : ℤ) < |m| := abs_pos.mpr hm
  have h8 : ((8 : ℕ) : ℤ) ≤ |m| := Int.le_of_dvd hpos habs
  norm_num at h8
  omega

theorem exists_collisionFreq_ne_zero_mod_eight {q : Fin 4 → α} (hq : collisionFreq q ≠ 0) :
    ∃ t, ((collisionFreq q t : ℤ) : ZMod 8) ≠ 0 := by
  obtain ⟨t, ht⟩ : ∃ t, collisionFreq q t ≠ 0 := by
    by_contra hcon
    exact hq (funext fun t => not_not.mp fun h => hcon ⟨t, h⟩)
  exact ⟨t, intCast_zmod_eight_ne_zero_of_abs_le ht
    (le_trans (collisionFreq_abs_le q t) (by norm_num))⟩

/-! ## The square -/

theorem trigLift_mul {κ σ : Type*} (P : Finset κ) (Q : Finset σ)
    (ν : κ → (α → ℤ)) (μ : σ → (α → ℤ)) (a : κ → ℂ) (b : σ → ℂ) (x : α → ℝ) :
    trigLift P ν a x * trigLift Q μ b x
      = trigLift (P ×ˢ Q) (fun r => ν r.1 + μ r.2) (fun r => a r.1 * b r.2) x := by
  classical
  rw [trigLift, trigLift, trigLift, Finset.sum_mul_sum, Finset.sum_product]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  rw [charLift_add_index]
  ring

/-- **The square of the collision is a trigonometric polynomial** indexed by eight register
points. -/
theorem phaseCollision_sq_eq_trigLift (e : ι → α → ℂ) (x : α → ℝ) :
    ((phaseCollision e x ^ 2 : ℝ) : ℂ)
      = trigLift (Finset.univ : Finset ((Fin 4 → α) × (Fin 4 → α)))
        (fun r => collisionFreq r.1 + collisionFreq r.2)
        (fun r => collisionCoeff e r.1 * collisionCoeff e r.2) x := by
  rw [Complex.ofReal_pow, sq, phaseCollision_eq_trigLift, trigLift_mul,
    Finset.univ_product_univ]

theorem card_freqSupport_add_collisionFreq_le (q q' : Fin 4 → α) :
    (Finset.univ.filter fun t => (collisionFreq q + collisionFreq q') t ≠ 0).card ≤ 8 := by
  classical
  have hsub : (Finset.univ.filter fun t => (collisionFreq q + collisionFreq q') t ≠ 0)
      ⊆ (Finset.univ.filter fun t => collisionFreq q t ≠ 0)
        ∪ (Finset.univ.filter fun t => collisionFreq q' t ≠ 0) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    rw [Finset.mem_union, Finset.mem_filter, Finset.mem_filter]
    by_contra hcon
    push Not at hcon
    exact ht.2 (by
      show collisionFreq q t + collisionFreq q' t = 0
      rw [hcon.1 (Finset.mem_univ t), hcon.2 (Finset.mem_univ t), add_zero])
  refine le_trans (Finset.card_le_card hsub) ?_
  refine le_trans (Finset.card_union_le _ _) ?_
  have h1 := card_freqSupport_collisionFreq_le q
  have h2 := card_freqSupport_collisionFreq_le q'
  omega

theorem exists_add_collisionFreq_ne_zero_mod_eight {q q' : Fin 4 → α}
    (hq : collisionFreq q + collisionFreq q' ≠ 0) :
    ∃ t, (((collisionFreq q + collisionFreq q') t : ℤ) : ZMod 8) ≠ 0 := by
  obtain ⟨t, ht⟩ : ∃ t, (collisionFreq q + collisionFreq q') t ≠ 0 := by
    by_contra hcon
    exact hq (funext fun t => not_not.mp fun h => hcon ⟨t, h⟩)
  refine ⟨t, intCast_zmod_eight_ne_zero_of_abs_le ht ?_⟩
  have h1 := collisionFreq_abs_le q t
  have h2 := collisionFreq_abs_le q' t
  have hadd : (collisionFreq q + collisionFreq q') t
      = collisionFreq q t + collisionFreq q' t := rfl
  rw [hadd]
  have habs := abs_add_le (collisionFreq q t) (collisionFreq q' t)
  omega

/-! ## The square on a plain index -/

/-- Two quadruples of register points are one octuple. -/
def pairToFin8 (α : Type*) : ((Fin 4 → α) × (Fin 4 → α)) ≃ (Fin 8 → α) :=
  (Equiv.sumArrowEquivProdArrow (Fin 4) (Fin 4) α).symm.trans
    (Equiv.arrowCongr finSumFinEquiv (Equiv.refl α))

/-- The frequency of one octuple term. -/
def sqFreq (r : Fin 8 → α) : α → ℤ :=
  collisionFreq ((pairToFin8 α).symm r).1 + collisionFreq ((pairToFin8 α).symm r).2

/-- The coefficient of one octuple term. -/
def sqCoeff (e : ι → α → ℂ) (r : Fin 8 → α) : ℂ :=
  collisionCoeff e ((pairToFin8 α).symm r).1 * collisionCoeff e ((pairToFin8 α).symm r).2

/-- **The square of the collision is a trigonometric polynomial on a plain octuple index.** -/
theorem phaseCollision_sq_eq_trigLift_fin8 (e : ι → α → ℂ) (x : α → ℝ) :
    ((phaseCollision e x ^ 2 : ℝ) : ℂ)
      = trigLift (Finset.univ : Finset (Fin 8 → α)) sqFreq (sqCoeff e) x := by
  rw [phaseCollision_sq_eq_trigLift, trigLift, trigLift]
  refine Eq.trans ?_ (Equiv.sum_comp (pairToFin8 α)
    (fun s : Fin 8 → α => sqCoeff e s * charLift (sqFreq s) x))
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [sqCoeff, sqFreq, Equiv.symm_apply_apply]

theorem card_freqSupport_sqFreq_le (r : Fin 8 → α) :
    (Finset.univ.filter fun t => sqFreq r t ≠ 0).card ≤ 8 :=
  card_freqSupport_add_collisionFreq_le _ _

theorem exists_sqFreq_ne_zero_mod_eight {r : Fin 8 → α} (hr : sqFreq r ≠ 0) :
    ∃ t, ((sqFreq r t : ℤ) : ZMod 8) ≠ 0 :=
  exists_add_collisionFreq_ne_zero_mod_eight hr

end GaloisForLFunctions.HTGeometry

end
