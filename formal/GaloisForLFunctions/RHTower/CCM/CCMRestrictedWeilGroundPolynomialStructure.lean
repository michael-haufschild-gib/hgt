import GaloisForLFunctions.RHTower.CCM.CCMRestrictedWeilGroundZeroQuadrature

/-!
# The polar ground level of the restricted Weil form is a polynomial module

At a positive aperture `a`, let `M_a` be the polar ground subspace of the restricted Weil form
on the CCM form domain (finite-dimensional, `finiteDimensional_groundSubmodule`), `d = dim M_a`.

**Theorem** (`exists_groundGenerator`).  There is a nonzero polar ground state `G` whose
transform has only real zeros off `w_{±1/2}`, such that the transform of every polar ground
state is `P · f̂_G` on the real line with `deg P < d`, and for every `k < d` some polar ground
state has transform `P · f̂_G` with `P` monic of degree `k`.  Thus
`M_a ≅ {P · f̂_G : deg P < d}`: the continuous form of the Iohvidov–Pisarenko structure of the
minimal eigenspace of a Hermitian Toeplitz matrix.

**Corollary** (`finrank_groundSubmodule_eq_one_iff`).  The polar ground level is simple iff no
polar ground state has transform `(t − c) f̂_G(t)` for a nonzero ground state `G`.

**Proof.**  Evaluation at the `d − 1` points `i(k + 2)` has a nontrivial kernel on `M_a`.
Dividing a kernel vector `u` successively at these points (`exists_div_prod`) gives ground
states `v_k` with `f̂_u = ∏_{i<k}(w − z_i) f̂_{v_k}`.  They are linearly independent
(`eq_zero_of_sum_div_prod`), hence a basis, and `f̂_{v_k} = ∏_{k≤i<d−1}(w − z_i) f̂_G` with
`G = v_{d−1}`.  A non-real non-polar zero `z` of `f̂_G` would make `f̂_G/(w − z) = P f̂_G`, i.e.
`(X − z)P = 1`, which is impossible.
-/

noncomputable section
open Complex MeasureTheory Set Filter Topology Polynomial
open scoped InnerProduct

namespace RHTower.CCMGroundStructure

open GaloisForLFunctions.HTGeometry.FourierZeroFlip
open GaloisForLFunctions.HTGeometry.FourierLaplaceDivision
open RHTower.CCMRealRootedGround RHTower.CCMGroundQuadrature

variable (a : SuzukiPositiveAperture)

/-- The transform on the real line determines the form-domain vector. -/
theorem eq_of_transform_eq {u v : CCMArchimedeanFormDomain a}
    (h : ∀ t : ℝ, unitaryLaplace (timeRep a u) t = unitaryLaplace (timeRep a v) t) : u = v := by
  have hae : ((u.1 : CCMArchimedeanFourierL2) : ℝ → ℂ) =ᵐ[volume]
      ((v.1 : CCMArchimedeanFourierL2) : ℝ → ℂ) :=
    (freq_ae a u).trans ((show (fun ξ : ℝ => unitaryLaplace (timeRep a u) ξ) =ᵐ[volume]
      fun ξ : ℝ => unitaryLaplace (timeRep a v) ξ from Eventually.of_forall h).trans
        (freq_ae a v).symm)
  exact Subtype.ext (Lp.ext (ccmArchimedeanFormMeasure_absolutelyContinuous_volume.ae_le hae))

theorem polarPoint_eq (s : ℝ) : polarPoint s = ((s / (2 * Real.pi) : ℝ) : ℂ) * I := by
  unfold polarPoint
  push_cast
  ring

theorem polarPoint_im (s : ℝ) : (polarPoint s).im = s / (2 * Real.pi) := by
  rw [polarPoint_eq, Complex.mul_I_im, Complex.ofReal_re]

/-- Division of a ground state at a non-real non-polar zero, with the identity on all of `ℂ`. -/
theorem exists_div_ground {u : CCMArchimedeanFormDomain a} (hu : IsPolarGround a u) {z : ℂ}
    (hz : unitaryLaplace (timeRep a u) z = 0) (him : z.im ≠ 0) (hp : z ≠ polarPoint (1 / 2))
    (hm : z ≠ polarPoint (-1 / 2)) :
    ∃ v : CCMArchimedeanFormDomain a, IsPolarGround a v ∧ ∀ w : ℂ,
      unitaryLaplace (timeRep a u) w = (w - z) * unitaryLaplace (timeRep a v) w := by
  obtain ⟨v, hv⟩ := exists_div a u hz
  refine ⟨v, isPolarGround_div a hu him hp hm hv, fun w => ?_⟩
  by_cases hw : w = z
  · rw [hw, hz, sub_self, zero_mul]
  · rw [hv w hw]
    field_simp [sub_ne_zero.mpr hw]

/-- Successive division at distinct non-real non-polar zeros. -/
theorem exists_div_prod {u : CCMArchimedeanFormDomain a} (hu : IsPolarGround a u) (zs : ℕ → ℂ)
    (hzs : ∀ i, (zs i).im ≠ 0 ∧ zs i ≠ polarPoint (1 / 2) ∧ zs i ≠ polarPoint (-1 / 2))
    (hinj : Function.Injective zs) :
    ∀ k : ℕ, (∀ i < k, unitaryLaplace (timeRep a u) (zs i) = 0) →
      ∃ v : CCMArchimedeanFormDomain a, IsPolarGround a v ∧ ∀ w : ℂ,
        unitaryLaplace (timeRep a u) w =
          (∏ i ∈ Finset.range k, (w - zs i)) * unitaryLaplace (timeRep a v) w
  | 0, _ => ⟨u, hu, fun w => by simp⟩
  | k + 1, hz => by
    obtain ⟨v, hv, hvw⟩ := exists_div_prod hu zs hzs hinj k (fun i hi => hz i (by omega))
    have hvz : unitaryLaplace (timeRep a v) (zs k) = 0 := by
      have h1 := hvw (zs k)
      rw [hz k (by omega)] at h1
      have hprod : ∏ i ∈ Finset.range k, (zs k - zs i) ≠ 0 := by
        rw [Finset.prod_ne_zero_iff]
        intro i hi
        refine sub_ne_zero.mpr fun h => ?_
        have := hinj h
        rw [Finset.mem_range] at hi
        omega
      exact (mul_eq_zero.mp h1.symm).resolve_left hprod
    obtain ⟨v', hv', hvw'⟩ := exists_div_ground a hv hvz (hzs k).1 (hzs k).2.1 (hzs k).2.2
    refine ⟨v', hv', fun w => ?_⟩
    rw [hvw w, hvw' w, Finset.prod_range_succ]
    ring

/-- The division points `i(k + 2)`. -/
def divPoint (k : ℕ) : ℂ := I * ((k : ℂ) + 2)

theorem divPoint_im (k : ℕ) : (divPoint k).im = (k : ℝ) + 2 := by
  simp [divPoint]

theorem divPoint_admissible (k : ℕ) : (divPoint k).im ≠ 0 ∧ divPoint k ≠ polarPoint (1 / 2) ∧
    divPoint k ≠ polarPoint (-1 / 2) := by
  have hpi := Real.pi_gt_three
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  refine ⟨by rw [divPoint_im]; positivity, fun h => ?_, fun h => ?_⟩
  · have := congrArg Complex.im h
    rw [divPoint_im, polarPoint_im] at this
    have h2 : (1 / 2 : ℝ) / (2 * Real.pi) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith
  · have := congrArg Complex.im h
    rw [divPoint_im, polarPoint_im] at this
    have h2 : (-1 / 2 : ℝ) / (2 * Real.pi) < 1 := by
      rw [div_lt_one (by positivity)]; linarith
    linarith

theorem divPoint_injective : Function.Injective divPoint := by
  intro i j h
  have := congrArg Complex.im h
  rw [divPoint_im, divPoint_im] at this
  exact_mod_cast (add_right_cancel this)

theorem ofReal_sub_divPoint_ne_zero (t : ℝ) (k : ℕ) : (t : ℂ) - divPoint k ≠ 0 :=
  sub_ne_zero.mpr (ne_of_im_ne_zero t (divPoint_admissible k).1)

/-- **Structure of the polar ground level.**  At every aperture there is a real-rooted polar
ground state `G` (zeros real off `w_{±1/2}`) such that every polar ground state has transform
`P · f̂_G` on the real line for a polynomial `P` of degree below the ground multiplicity. -/
theorem exists_groundGenerator :
    ∃ G : CCMArchimedeanFormDomain a, IsPolarGround a G ∧
      ccmArchimedeanFormToAperture a G ≠ 0 ∧
      (∀ w : ℂ, unitaryLaplace (timeRep a G) w = 0 → w ≠ polarPoint (1 / 2) →
        w ≠ polarPoint (-1 / 2) → w.im = 0) ∧
      (∀ u : CCMArchimedeanFormDomain a, IsPolarGround a u →
        ∃ P : ℂ[X], P.natDegree < Module.finrank ℂ (groundSubmodule a) ∧
          ∀ t : ℝ, unitaryLaplace (timeRep a u) t =
            P.eval (t : ℂ) * unitaryLaplace (timeRep a G) t) ∧
      ∀ k < Module.finrank ℂ (groundSubmodule a), ∃ u : CCMArchimedeanFormDomain a,
        IsPolarGround a u ∧ ∃ P : ℂ[X], P.Monic ∧ P.natDegree = k ∧
          ∀ t : ℝ, unitaryLaplace (timeRep a u) t =
            P.eval (t : ℂ) * unitaryLaplace (timeRep a G) t := by
  classical
  haveI := finiteDimensional_groundSubmodule a
  set d := Module.finrank ℂ (groundSubmodule a) with hd
  obtain ⟨u₀, hu₀, hne₀, -⟩ := exists_realRooted_polarGround a
  have hd1 : 1 ≤ d := by
    have hx : (⟨u₀, hu₀⟩ : groundSubmodule a) ≠ 0 := by
      intro h
      apply hne₀
      have : u₀ = 0 := congrArg Subtype.val h
      rw [this, map_zero]
    exact Module.finrank_pos_iff_exists_ne_zero.mpr ⟨_, hx⟩
  let ψ : groundSubmodule a →ₗ[ℂ] (Fin (d - 1) → ℂ) :=
    LinearMap.pi fun i => (evalAt a (divPoint i)).comp (groundSubmodule a).subtype
  have hker : LinearMap.ker ψ ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt (by
    rw [Module.finrank_fin_fun]; omega)
  obtain ⟨u, huker, hune⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hker
  have hu : IsPolarGround a u.1 := u.2
  have hzu : ∀ i < d - 1, unitaryLaplace (timeRep a u.1) (divPoint i) = 0 := by
    intro i hi
    have := congrFun (LinearMap.mem_ker.mp huker) ⟨i, hi⟩
    simpa [ψ, evalAt_apply] using this
  have hJu : ccmArchimedeanFormToAperture a u.1 ≠ 0 := by
    intro h
    apply hune
    exact Subtype.ext (ccmArchimedeanFormToAperture_injective a
      (by rw [h, Submodule.coe_zero, map_zero]))
  have hchain : ∀ k : ℕ, ∃ v : CCMArchimedeanFormDomain a, k ≤ d - 1 →
      IsPolarGround a v ∧ ∀ w : ℂ, unitaryLaplace (timeRep a u.1) w =
        (∏ i ∈ Finset.range k, (w - divPoint i)) * unitaryLaplace (timeRep a v) w := by
    intro k
    by_cases hk : k ≤ d - 1
    · obtain ⟨v, hv, hvw⟩ := exists_div_prod a hu divPoint divPoint_admissible
        divPoint_injective k (fun i hi => hzu i (by omega))
      exact ⟨v, fun _ => ⟨hv, hvw⟩⟩
    · exact ⟨0, fun h => absurd h hk⟩
  choose v hv using hchain
  obtain ⟨hG, hGw⟩ := hv (d - 1) le_rfl
  set G := v (d - 1) with hGdef
  have hrel : ∀ k ≤ d - 1, ∀ t : ℝ, unitaryLaplace (timeRep a (v k)) t =
      (∏ i ∈ Finset.Ico k (d - 1), ((t : ℂ) - divPoint i)) *
        unitaryLaplace (timeRep a G) t := by
    intro k hk t
    have h1 := (hv k hk).2 t
    have h2 := hGw t
    rw [← Finset.prod_range_mul_prod_Ico _ hk, mul_assoc] at h2
    have hp : ∏ i ∈ Finset.range k, ((t : ℂ) - divPoint i) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun i _ => ofReal_sub_divPoint_ne_zero t i
    exact mul_left_cancel₀ hp (h1.symm.trans h2)
  have hJG : ccmArchimedeanFormToAperture a G ≠ 0 := by
    intro hJ
    have hG0 : G = 0 := ccmArchimedeanFormToAperture_injective a (by rw [hJ, map_zero])
    obtain ⟨t, ht⟩ := exists_real_ne_zero a hJu
    apply ht
    rw [hGw t, hG0, unitaryLaplace_timeRep_zero, mul_zero]
  let b : Fin d → groundSubmodule a := fun k => ⟨v k, (hv k (by omega)).1⟩
  have hli : LinearIndependent ℂ b := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    let c' : ℕ → ℂ := fun j => if h : j < d then c ⟨j, h⟩ else 0
    have hreal : ∀ j < d - 1, ∀ t : ℝ, (t : ℂ) - divPoint j ≠ 0 :=
      fun j _ t => ofReal_sub_divPoint_ne_zero t j
    have hsum : ∀ t : ℝ, ∑ j ∈ Finset.range (d - 1 + 1), c' j *
        (unitaryLaplace (timeRep a u.1) t / ∏ l ∈ Finset.range j, ((t : ℂ) - divPoint l)) = 0 := by
      intro t
      have h0 := congrArg (fun x : groundSubmodule a => evalAt a t x.1) hc
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul,
        Submodule.coe_zero, map_zero] at h0
      rw [Nat.sub_add_cancel hd1, ← h0, ← Fin.sum_univ_eq_sum_range (fun j => c' j *
        (unitaryLaplace (timeRep a u.1) t / ∏ l ∈ Finset.range j, ((t : ℂ) - divPoint l)))]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [c', dif_pos j.isLt, Fin.eta]
      congr 1
      have h1 := (hv j (by omega)).2 t
      have hp : ∏ l ∈ Finset.range j, ((t : ℂ) - divPoint l) ≠ 0 :=
        Finset.prod_ne_zero_iff.mpr fun l _ => ofReal_sub_divPoint_ne_zero t l
      rw [evalAt_apply, h1]
      field_simp
      rfl
    have := eq_zero_of_sum_div_prod (infinite_real_ne_zero a hJu) divPoint (d - 1) hreal c' hsum i
      (by omega)
    simp only [c', dif_pos i.isLt, Fin.eta] at this
    exact this
  have hspan := hli.span_eq_top_of_card_eq_finrank' (by rw [Fintype.card_fin])
  have hstruct : ∀ u' : CCMArchimedeanFormDomain a, IsPolarGround a u' →
      ∃ P : ℂ[X], P.natDegree < d ∧ ∀ t : ℝ, unitaryLaplace (timeRep a u') t =
        P.eval (t : ℂ) * unitaryLaplace (timeRep a G) t := by
    intro u' hu'
    have hmem : (⟨u', hu'⟩ : groundSubmodule a) ∈ Submodule.span ℂ (Set.range b) := by
      rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).mp hmem
    refine ⟨∑ k : Fin d, Polynomial.C (c k) *
      ∏ i ∈ Finset.Ico (k : ℕ) (d - 1), (X - Polynomial.C (divPoint i)), ?_, fun t => ?_⟩
    · refine lt_of_le_of_lt (Polynomial.natDegree_sum_le_of_forall_le _ _ (n := d - 1)
        fun k _ => ?_) (by omega)
      refine (Polynomial.natDegree_C_mul_le _ _).trans ((Polynomial.natDegree_prod_le _ _).trans ?_)
      calc ∑ i ∈ Finset.Ico (k : ℕ) (d - 1), (X - Polynomial.C (divPoint i)).natDegree
          = ∑ i ∈ Finset.Ico (k : ℕ) (d - 1), 1 :=
            Finset.sum_congr rfl fun i _ => Polynomial.natDegree_X_sub_C _
        _ = d - 1 - k := by simp
        _ ≤ d - 1 := Nat.sub_le _ _
    · have h0 := congrArg (fun x : groundSubmodule a => evalAt a t x.1) hc
      simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, smul_eq_mul] at h0
      rw [evalAt_apply] at h0
      rw [← h0, Polynomial.eval_finsetSum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [evalAt_apply, hrel k (by omega) t, Polynomial.eval_mul, Polynomial.eval_C,
        Polynomial.eval_prod]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
      ring
  refine ⟨G, hG, hJG, fun w hw hp hm => ?_, hstruct, fun k hk => ?_⟩
  swap
  · refine ⟨v (d - 1 - k), (hv _ (by omega)).1,
      ∏ i ∈ Finset.Ico (d - 1 - k) (d - 1), (X - Polynomial.C (divPoint i)),
      Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _, ?_, fun t => ?_⟩
    · rw [Polynomial.natDegree_prod _ _ fun i _ => Polynomial.X_sub_C_ne_zero _]
      simp only [Polynomial.natDegree_X_sub_C, Finset.sum_const, Nat.card_Ico, smul_eq_mul,
        mul_one]
      omega
    · rw [hrel _ (by omega) t, Polynomial.eval_prod]
      simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]
  by_contra him
  obtain ⟨G', hG', hG'w⟩ := exists_div_ground a hG hw him hp hm
  obtain ⟨P, -, hP⟩ := hstruct G' hG'
  have hroots : {z : ℂ | ((X - Polynomial.C w) * P - 1).IsRoot z}.Infinite := by
    refine ((infinite_real_ne_zero a hJG).image Complex.ofReal_injective.injOn).mono ?_
    rintro _ ⟨t, ht, rfl⟩
    simp only [mem_setOf_eq, Polynomial.IsRoot.def, Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_one]
    have h1 := hG'w t
    rw [hP t] at h1
    have hone : ((t : ℂ) - w) * P.eval (t : ℂ) = 1 := by
      apply mul_right_cancel₀ (show unitaryLaplace (timeRep a G) t ≠ 0 from ht)
      linear_combination -h1
    rw [hone, sub_self]
  have hprod : (X - Polynomial.C w) * P = 1 :=
    sub_eq_zero.mp (Polynomial.eq_zero_of_infinite_isRoot _ hroots)
  have hP0 : P ≠ 0 := by
    rintro rfl
    simp at hprod
  have hdeg := congrArg Polynomial.natDegree hprod
  rw [Polynomial.natDegree_mul (Polynomial.X_sub_C_ne_zero w) hP0, Polynomial.natDegree_X_sub_C,
    Polynomial.natDegree_one] at hdeg
  omega

/-- **Simplicity criterion.**  The polar ground level is simple iff no polar ground state has
transform `(t − c) f̂_G(t)` for a nonzero ground state `G`. -/
theorem finrank_groundSubmodule_eq_one_iff :
    Module.finrank ℂ (groundSubmodule a) = 1 ↔
      ∀ G u : CCMArchimedeanFormDomain a, IsPolarGround a G → ccmArchimedeanFormToAperture a G ≠ 0 →
        IsPolarGround a u → ∀ c : ℂ, ¬ ∀ t : ℝ, unitaryLaplace (timeRep a u) t =
          ((t : ℂ) - c) * unitaryLaplace (timeRep a G) t := by
  classical
  haveI := finiteDimensional_groundSubmodule a
  constructor
  · intro hd G u hG hJG hu c hc
    have hGne : (⟨G, hG⟩ : groundSubmodule a) ≠ 0 := by
      intro h
      apply hJG
      have : G = 0 := congrArg Subtype.val h
      rw [this, map_zero]
    obtain ⟨μ, hμ⟩ := (finrank_eq_one_iff_of_nonzero' _ hGne).mp hd ⟨u, hu⟩
    have hval : ∀ t : ℝ, unitaryLaplace (timeRep a u) t = μ * unitaryLaplace (timeRep a G) t := by
      intro t
      have h0 := congrArg (fun x : groundSubmodule a => evalAt a t x.1) hμ
      simp only [Submodule.coe_smul, map_smul, smul_eq_mul, evalAt_apply] at h0
      exact h0.symm
    obtain ⟨t₁, ht₁, t₂, ht₂, hne⟩ : ∃ t₁ ∈ {t : ℝ | unitaryLaplace (timeRep a G) t ≠ 0},
        ∃ t₂ ∈ {t : ℝ | unitaryLaplace (timeRep a G) t ≠ 0}, t₁ ≠ t₂ :=
      (infinite_real_ne_zero a hJG).nontrivial
    have e1 : (t₁ : ℂ) - c = μ := mul_right_cancel₀ ht₁ ((hc t₁).symm.trans (hval t₁))
    have e2 : (t₂ : ℂ) - c = μ := mul_right_cancel₀ ht₂ ((hc t₂).symm.trans (hval t₂))
    apply hne
    exact_mod_cast sub_left_injective (e1.trans e2.symm)
  · intro h
    obtain ⟨G, hG, hJG, -, -, hmul⟩ := exists_groundGenerator a
    have hd1 : 1 ≤ Module.finrank ℂ (groundSubmodule a) :=
      Module.finrank_pos_iff_exists_ne_zero.mpr ⟨⟨G, hG⟩, fun h0 => hJG (by
        have : G = 0 := congrArg Subtype.val h0
        rw [this, map_zero])⟩
    by_contra hne
    obtain ⟨u, hu, P, hPm, hPd, hP⟩ := hmul 1 (by omega)
    have hP' : P = X - Polynomial.C (-(P.coeff 0)) := by
      rw [Polynomial.Monic.eq_X_add_C hPm hPd]
      simp
    refine h G u hG hJG hu (-(P.coeff 0)) fun t => ?_
    rw [hP t, hP']
    simp

end RHTower.CCMGroundStructure
