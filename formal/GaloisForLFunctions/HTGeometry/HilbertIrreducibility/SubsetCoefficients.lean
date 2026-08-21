/-
# Subset coefficients: the two structural steps

Steps 1 and 2 of Coleman--Zwald's proof.

* `irreducible_fibre_of_not_rational` (step 2): if for every proper nonempty subset `S` of the
  branches some coefficient of `∏_{i∈S} (Y − uᵢ(b))` is irrational, then the fibre `f(b, ·)` is
  irreducible over `ℚ` — a rational factor would have to be one of these subset products.
* `exists_not_ratGerm` (step 1): for every proper nonempty subset `S`, some coefficient of
  `∏_{i∈S} (Y − uᵢ(s))` is not a rational function of `s`; otherwise clearing denominators produces
  a genuine common factor of `f` with a polynomial of intermediate degree, and the resultant
  argument contradicts irreducibility of `f` over `ℚ(X)`.
-/
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.AnalyticBranches
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.IntegralCoefficients
import GaloisForLFunctions.HTGeometry.HilbertIrreducibility.Core
import Mathlib.RingTheory.Localization.FractionRing

namespace GaloisForLFunctions.HTGeometry.HilbertIrreducibility

open Polynomial Filter Topology

/-- Coefficient-wise base change `ℤ[X][Y] → ℚ[X][Y]`. -/
noncomputable def toQ (f : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℚ) :=
  f.map (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- Coefficient-wise base change `ℤ[X][Y] → ℂ[X][Y]`. -/
noncomputable def toC (f : Polynomial (Polynomial ℤ)) : Polynomial (Polynomial ℂ) :=
  f.map (Polynomial.mapRingHom (Int.castRingHom ℂ))

theorem map_fibre_toQ (f : Polynomial (Polynomial ℤ)) (b : ℚ) :
    ((toQ f).map (Polynomial.evalRingHom b)).map (Rat.castHom ℂ)
      = (toC f).map (Polynomial.evalRingHom ((b : ℚ) : ℂ)) := by
  rw [toQ, toC, Polynomial.map_map, Polynomial.map_map, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
    Polynomial.eval_map]
  rw [Polynomial.hom_eval₂]
  have hcomp : (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ :=
    RingHom.ext fun z => by simp
  rw [hcomp]
  simp

/-- A complex polynomial vanishing on a neighbourhood of a point is zero. -/
theorem polynomial_eq_zero_of_eventually {p : Polynomial ℂ} {s₀ : ℂ}
    (h : ∀ᶠ s in 𝓝 s₀, p.eval s = 0) : p = 0 := by
  obtain ⟨ρ, hρ, hball⟩ := Metric.eventually_nhds_iff.mp h
  refine Polynomial.eq_zero_of_infinite_isRoot p ?_
  set F : ℕ → ℂ := fun m => s₀ + (((ρ / 2) / (m + 1) : ℝ) : ℂ) with hF
  have hinj : Function.Injective F := by
    intro a b hab
    rw [hF] at hab
    have h1 : (((ρ / 2) / (a + 1) : ℝ) : ℂ) = (((ρ / 2) / (b + 1) : ℝ) : ℂ) := by
      simpa using hab
    have h2 : (ρ / 2) / ((a : ℝ) + 1) = (ρ / 2) / ((b : ℝ) + 1) := by exact_mod_cast h1
    have ha : (0 : ℝ) < (a : ℝ) + 1 := by positivity
    have hb : (0 : ℝ) < (b : ℝ) + 1 := by positivity
    have hρ2 : (0 : ℝ) < ρ / 2 := by positivity
    field_simp at h2
    have h3 : (b : ℝ) + 1 = (a : ℝ) + 1 := h2
    have h4 : (a : ℝ) = (b : ℝ) := by linarith
    exact_mod_cast h4
  refine Set.infinite_of_injective_forall_mem hinj ?_
  intro m
  have hmem : dist (F m) s₀ < ρ := by
    rw [hF, Complex.dist_eq, add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs]
    have h1 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
    rw [abs_of_pos (by positivity)]
    calc (ρ / 2) / ((m : ℝ) + 1) ≤ ρ / 2 := by
          refine div_le_self (by positivity) ?_
          linarith
      _ < ρ := by linarith
  exact hball hmem

/-- **Step 2.**  Irrational subset coefficients force the fibre to be irreducible. -/
theorem irreducible_fibre_of_not_rational {f : Polynomial (Polynomial ℤ)} {n : ℕ}
    (hn1 : 1 ≤ n) {u : Fin n → ℂ → ℂ} {b : ℚ}
    (hdeg : ((toC f).map (Polynomial.evalRingHom ((b : ℚ) : ℂ))).natDegree = n)
    (hinj : Function.Injective fun i => u i ((b : ℚ) : ℂ))
    (hroots : ((toC f).map (Polynomial.evalRingHom ((b : ℚ) : ℂ))).roots
        = Multiset.map (fun i => u i ((b : ℚ) : ℂ)) (Finset.univ : Finset (Fin n)).val)
    (hnr : ∀ S : Finset (Fin n), S.Nonempty → S ≠ Finset.univ → ∃ k : ℕ,
        ¬ ∃ c : ℚ, (∏ i ∈ S, (Polynomial.X - Polynomial.C (u i ((b : ℚ) : ℂ)))).coeff k
          = (c : ℂ)) :
    Irreducible ((toQ f).map (Polynomial.evalRingHom b)) := by
  classical
  set g : Polynomial ℚ := (toQ f).map (Polynomial.evalRingHom b) with hg
  set gC : Polynomial ℂ := (toC f).map (Polynomial.evalRingHom ((b : ℚ) : ℂ)) with hgC
  have hmap : g.map (Rat.castHom ℂ) = gC := map_fibre_toQ f b
  have hcastinj : Function.Injective (Rat.castHom ℂ) := (Rat.castHom ℂ).injective
  have hgdeg : g.natDegree = n := by
    have h := Polynomial.natDegree_map_eq_of_injective hcastinj g
    rw [hmap] at h
    rw [← h, hdeg]
  have hgne : g ≠ 0 := by
    intro h
    rw [h] at hgdeg
    simp only [Polynomial.natDegree_zero] at hgdeg
    omega
  have hgCne : gC ≠ 0 := by
    rw [← hmap]
    exact fun h => hgne (Polynomial.map_eq_zero_iff hcastinj |>.mp h)
  have hnodup : gC.roots.Nodup := by
    rw [hroots]
    exact Multiset.Nodup.map hinj (Finset.univ (α := Fin n)).nodup
  have hunit : ∀ p : Polynomial ℚ, p ≠ 0 → p.natDegree = 0 → IsUnit p := by
    intro p hp h0
    obtain ⟨a, ha⟩ := Polynomial.natDegree_eq_zero.mp h0
    have hane : a ≠ 0 := by
      intro h; rw [h, map_zero] at ha; exact hp ha.symm
    rw [← ha]
    exact Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hane)
  constructor
  · intro hu
    have := Polynomial.natDegree_eq_zero_of_isUnit hu
    omega
  · intro g₁ g₂ hfac
    by_contra hcon
    push_neg at hcon
    obtain ⟨hu1, hu2⟩ := hcon
    have hg1ne : g₁ ≠ 0 := by
      intro h; rw [h, zero_mul] at hfac; exact hgne hfac
    have hg2ne : g₂ ≠ 0 := by
      intro h; rw [h, mul_zero] at hfac; exact hgne hfac
    have hd1 : 1 ≤ g₁.natDegree := by
      by_contra hc
      push_neg at hc
      exact hu1 (hunit g₁ hg1ne (by omega))
    have hd2 : 1 ≤ g₂.natDegree := by
      by_contra hc
      push_neg at hc
      exact hu2 (hunit g₂ hg2ne (by omega))
    have hsum : g₁.natDegree + g₂.natDegree = n := by
      rw [← hgdeg, hfac, Polynomial.natDegree_mul hg1ne hg2ne]
    set g₁C : Polynomial ℂ := g₁.map (Rat.castHom ℂ) with hg1C
    have hg1Cdeg : g₁C.natDegree = g₁.natDegree :=
      Polynomial.natDegree_map_eq_of_injective hcastinj g₁
    have hg1Cne : g₁C ≠ 0 := fun h => hg1ne (Polynomial.map_eq_zero_iff hcastinj |>.mp h)
    have hdvd : g₁C ∣ gC := by
      rw [← hmap, hfac, Polynomial.map_mul]
      exact Dvd.intro _ rfl
    have hle : g₁C.roots ≤ gC.roots := Polynomial.roots.le_of_dvd hgCne hdvd
    set S : Finset (Fin n) :=
      Finset.univ.filter (fun i => u i ((b : ℚ) : ℂ) ∈ g₁C.roots) with hS
    have hrootsEq : g₁C.roots = Multiset.map (fun i => u i ((b : ℚ) : ℂ)) S.val := by
      refine (Multiset.Nodup.ext (Multiset.nodup_of_le hle hnodup) ?_).mpr ?_
      · exact Multiset.Nodup.map hinj (Finset.nodup S)
      · intro x
        constructor
        · intro hx
          have hxM : x ∈ gC.roots := Multiset.mem_of_le hle hx
          rw [hroots] at hxM
          obtain ⟨i, _, hi⟩ := Multiset.mem_map.mp hxM
          refine Multiset.mem_map.mpr ⟨i, ?_, hi⟩
          have hmem : u i ((b : ℚ) : ℂ) ∈ g₁C.roots := by rw [hi]; exact hx
          rw [hS, Finset.mem_val, Finset.mem_filter]
          exact ⟨Finset.mem_univ i, hmem⟩
        · intro hx
          obtain ⟨i, hi, hix⟩ := Multiset.mem_map.mp hx
          rw [hS, Finset.mem_val, Finset.mem_filter] at hi
          rw [← hix]
          exact hi.2
    have hcard : S.card = g₁.natDegree := by
      have h1 : Multiset.card g₁C.roots = g₁C.natDegree :=
        IsAlgClosed.card_roots_eq_natDegree
      rw [hrootsEq, Multiset.card_map] at h1
      rw [← hg1Cdeg, ← h1]
      rfl
    have hSne : S.Nonempty := by
      rw [← Finset.card_pos, hcard]; omega
    have hSuniv : S ≠ Finset.univ := by
      intro h
      have : S.card = n := by rw [h]; simp
      omega
    obtain ⟨k, hk⟩ := hnr S hSne hSuniv
    apply hk
    -- the subset product is `g₁C` up to its leading coefficient
    have hsplit : g₁C = Polynomial.C g₁C.leadingCoeff
        * (Multiset.map (fun a => Polynomial.X - Polynomial.C a) g₁C.roots).prod :=
      Polynomial.Splits.eq_prod_roots (IsAlgClosed.splits g₁C)
    have hprodeq : (Multiset.map (fun a => Polynomial.X - Polynomial.C a) g₁C.roots).prod
        = ∏ i ∈ S, (Polynomial.X - Polynomial.C (u i ((b : ℚ) : ℂ))) := by
      rw [hrootsEq, Multiset.map_map]
      rfl
    rw [hprodeq] at hsplit
    have hlcne : g₁C.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr hg1Cne
    have hcoef : (∏ i ∈ S, (Polynomial.X - Polynomial.C (u i ((b : ℚ) : ℂ)))).coeff k
        = (g₁C.leadingCoeff)⁻¹ * g₁C.coeff k := by
      have h1 : g₁C.coeff k = g₁C.leadingCoeff *
          (∏ i ∈ S, (Polynomial.X - Polynomial.C (u i ((b : ℚ) : ℂ)))).coeff k := by
        nth_rewrite 1 [hsplit]
        rw [Polynomial.coeff_C_mul]
      rw [h1, ← mul_assoc, inv_mul_cancel₀ hlcne, one_mul]
    refine ⟨(g₁.leadingCoeff)⁻¹ * g₁.coeff k, ?_⟩
    rw [hcoef]
    have hlc : g₁C.leadingCoeff = ((g₁.leadingCoeff : ℚ) : ℂ) := by
      rw [hg1C, Polynomial.leadingCoeff, Polynomial.leadingCoeff, hg1Cdeg, Polynomial.coeff_map]
      rfl
    have hck : g₁C.coeff k = ((g₁.coeff k : ℚ) : ℂ) := by
      rw [hg1C, Polynomial.coeff_map]; rfl
    rw [hlc, hck]
    push_cast
    ring

/-! ### Step 1 -/

/-- Evaluation `ℚ[X] → ℂ` at a complex point. -/
noncomputable def evalCHom (s : ℂ) : Polynomial ℚ →+* ℂ :=
  (Polynomial.aeval s : Polynomial ℚ →ₐ[ℚ] ℂ).toRingHom

theorem map_toQ_toC (f : Polynomial (Polynomial ℤ)) (s : ℂ) :
    (toQ f).map (evalCHom s) = (toC f).map (Polynomial.evalRingHom s) := by
  rw [toQ, toC, Polynomial.map_map, Polynomial.map_map]
  congr 1
  refine RingHom.ext fun p => ?_
  simp only [RingHom.comp_apply, Polynomial.coe_mapRingHom, Polynomial.coe_evalRingHom,
    Polynomial.eval_map, evalCHom, AlgHom.toRingHom_eq_coe, RingHom.coe_coe,
    Polynomial.aeval_def]
  rw [Polynomial.eval₂_map]
  congr 1

theorem natDegree_toQ (f : Polynomial (Polynomial ℤ)) : (toQ f).natDegree = f.natDegree := by
  refine Polynomial.natDegree_map_eq_of_injective ?_ f
  intro a b hab
  exact Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective hab

/-- **Step 1.**  For every proper nonempty subset of the branches, some coefficient of the
corresponding partial product is not a rational function of the parameter. -/
theorem exists_not_ratGerm {f : Polynomial (Polynomial ℤ)} {n : ℕ} (hn : f.natDegree = n)
    (hirr : Irreducible ((toQ f).map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))))
    {s₀ : ℂ} {u : Fin n → ℂ → ℂ}
    (hprod : ∀ᶠ s in 𝓝 s₀, ∃ c : ℂ, c ≠ 0 ∧ (toC f).map (Polynomial.evalRingHom s)
        = Polynomial.C c * ∏ i, (Polynomial.X - Polynomial.C (u i s)))
    (hdegs : ∀ᶠ s in 𝓝 s₀, ((toC f).map (Polynomial.evalRingHom s)).natDegree = n)
    (S : Finset (Fin n)) (hS1 : S.Nonempty) (hS2 : S ≠ Finset.univ) :
    ∃ k : ℕ, ¬ IsRatGerm s₀
      (fun s => (∏ i ∈ S, (Polynomial.X - Polynomial.C (u i s))).coeff k) := by
  classical
  by_contra hcon
  push_neg at hcon
  set d : ℕ := S.card with hd
  have hd1 : 1 ≤ d := Finset.card_pos.mpr hS1
  have hcardle : S.card ≤ n := by
    have h := Finset.card_le_card (Finset.subset_univ S)
    simpa using h
  have hdn : d < n := by
    rcases lt_or_eq_of_le hcardle with h | h
    · exact h
    · exact absurd (Finset.eq_univ_of_card S (by simpa using h)) hS2
  have hn2 : 2 ≤ n := by omega
  choose p q hq hrel using hcon
  set Dpoly : Polynomial ℚ := ∏ k ∈ Finset.range d, q k with hDpoly
  have hD0 : Polynomial.aeval s₀ Dpoly ≠ 0 := by
    rw [hDpoly, map_prod]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hq k
  set Bc : ℕ → Polynomial ℚ := fun k =>
    if k = d then Dpoly else p k * ∏ j ∈ (Finset.range d).erase k, q j with hBc
  set Bhat : Polynomial (Polynomial ℚ) :=
    ∑ k ∈ Finset.range (d + 1), Polynomial.monomial k (Bc k) with hBhat
  have hBcoeff : ∀ m, Bhat.coeff m = if m ≤ d then Bc m else 0 := by
    intro m
    rw [hBhat, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range (d + 1)) m (fun k => Bc k)]
    by_cases hm : m ≤ d
    · rw [if_pos (Finset.mem_range.mpr (by omega)), if_pos hm]
    · rw [if_neg (by simpa using by omega : m ∉ Finset.range (d + 1)), if_neg hm]
  have hBd : Bhat.coeff d = Dpoly := by rw [hBcoeff d, if_pos le_rfl, hBc]; simp
  have hBdegle : Bhat.natDegree ≤ d := by
    refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun m hm => ?_
    rw [hBcoeff m, if_neg (by exact_mod_cast Nat.not_le.mpr (by exact_mod_cast hm))]
  have hDne : Dpoly ≠ 0 := by
    intro h
    apply hD0
    rw [h, map_zero]
  have hBdeg : Bhat.natDegree = d :=
    le_antisymm hBdegle (Polynomial.le_natDegree_of_ne_zero (by rw [hBd]; exact hDne))
  -- the specialised identity `Bhat(s, ·) = D(s) · βS(s, ·)`
  have hbetaMonic : ∀ s : ℂ, (∏ i ∈ S, (Polynomial.X - Polynomial.C (u i s))).Monic := fun s =>
    Polynomial.monic_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C _
  have hbetaDeg : ∀ s : ℂ, (∏ i ∈ S, (Polynomial.X - Polynomial.C (u i s))).natDegree = d := by
    intro s
    rw [Polynomial.natDegree_prod_of_monic _ _ fun i _ => Polynomial.monic_X_sub_C (u i s)]
    simp [hd]
  have hDev : ∀ᶠ s in 𝓝 s₀, Polynomial.aeval s Dpoly ≠ 0 := by
    have hc : ContinuousAt (fun s : ℂ => Polynomial.aeval s Dpoly) s₀ :=
      (Dpoly.continuous_aeval).continuousAt
    exact hc.eventually_ne hD0
  have hBeq : ∀ᶠ s in 𝓝 s₀, Bhat.map (evalCHom s)
      = Polynomial.C (Polynomial.aeval s Dpoly)
        * ∏ i ∈ S, (Polynomial.X - Polynomial.C (u i s)) := by
    have hall : ∀ᶠ s in 𝓝 s₀, ∀ k ∈ Finset.range d,
        (Polynomial.aeval s (q k))
            * (∏ i ∈ S, (Polynomial.X - Polynomial.C (u i s))).coeff k
          = Polynomial.aeval s (p k) :=
      (Filter.eventually_all_finset _).mpr fun k _ => hrel k
    filter_upwards [hall] with s hs
    refine Polynomial.ext fun m => ?_
    rw [Polynomial.coeff_map, Polynomial.coeff_C_mul, hBcoeff m]
    by_cases hm : m ≤ d
    · rw [if_pos hm]
      rcases eq_or_lt_of_le hm with hmd | hmd
      · rw [hmd, hBc]
        simp only [if_pos rfl]
        have h1 : (∏ i ∈ S, (Polynomial.X - Polynomial.C (u i s))).coeff d = 1 := by
          have := (hbetaMonic s)
          rw [Polynomial.Monic, Polynomial.leadingCoeff, hbetaDeg s] at this
          exact this
        rw [h1, mul_one]
        rfl
      · have hmne : m ≠ d := Nat.ne_of_lt hmd
        rw [hBc]
        simp only [if_neg hmne]
        have hprodsplit : Polynomial.aeval s Dpoly
            = (Polynomial.aeval s (q m)) * ∏ j ∈ (Finset.range d).erase m,
                Polynomial.aeval s (q j) := by
          rw [hDpoly, map_prod]
          exact (Finset.mul_prod_erase _ _ (Finset.mem_range.mpr hmd)).symm
        have hrelm := hs m (Finset.mem_range.mpr hmd)
        show Polynomial.aeval s (p m * ∏ j ∈ (Finset.range d).erase m, q j) = _
        rw [map_mul, map_prod, hprodsplit, ← hrelm]
        ring
    · rw [if_neg hm, map_zero]
      have hz : (∏ i ∈ S, (Polynomial.X - Polynomial.C (u i s))).coeff m = 0 :=
        Polynomial.coeff_eq_zero_of_natDegree_lt (by rw [hbetaDeg s]; omega)
      rw [hz, mul_zero]
  -- the resultant vanishes identically
  set Res : Polynomial ℚ := Polynomial.resultant (toQ f) Bhat with hRes
  have hfQdeg : (toQ f).natDegree = n := by rw [natDegree_toQ, hn]
  have hResZero : Res = 0 := by
    have hev : ∀ᶠ s in 𝓝 s₀, (Res.map (Rat.castHom ℂ)).eval s = 0 := by
      filter_upwards [hprod, hdegs, hBeq, hDev] with s hc hdg hbe hdv
      obtain ⟨c, hcne, hceq⟩ := hc
      set β : Polynomial ℂ := ∏ i ∈ S, (Polynomial.X - Polynomial.C (u i s)) with hβ
      have hfCdeg : ((toQ f).map (evalCHom s)).natDegree = n := by
        rw [map_toQ_toC]; exact hdg
      have hBCdeg : (Bhat.map (evalCHom s)).natDegree = d := by
        rw [hbe, Polynomial.natDegree_C_mul hdv, hbetaDeg s]
      have hfCne : (toQ f).map (evalCHom s) ≠ 0 := by
        intro h
        rw [h] at hfCdeg
        simp only [Polynomial.natDegree_zero] at hfCdeg
        omega
      have hdvd1 : β ∣ (toQ f).map (evalCHom s) := by
        rw [map_toQ_toC, hceq]
        exact Dvd.dvd.mul_left (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.subset_univ S)) _
      have hdvd2 : β ∣ Bhat.map (evalCHom s) := by
        rw [hbe]
        exact Dvd.dvd.mul_left dvd_rfl _
      have hβunit : ¬ IsUnit β := by
        intro hu
        have := Polynomial.natDegree_eq_zero_of_isUnit hu
        rw [hbetaDeg s] at this
        omega
      have hncop : ¬ IsCoprime ((toQ f).map (evalCHom s)) (Bhat.map (evalCHom s)) := by
        intro hcop
        obtain ⟨x, y, hxy⟩ := hcop
        exact hβunit (isUnit_of_dvd_one (hxy ▸ (Dvd.dvd.add (hdvd1.mul_left x)
          (hdvd2.mul_left y))))
      have hzero : Polynomial.resultant ((toQ f).map (evalCHom s))
          (Bhat.map (evalCHom s)) = 0 :=
        Polynomial.resultant_eq_zero_iff.mpr ⟨Or.inl hfCne, hncop⟩
      have hdegeq1 : ((toQ f).map (evalCHom s)).natDegree = (toQ f).natDegree := by
        rw [hfCdeg, hfQdeg]
      have hdegeq2 : (Bhat.map (evalCHom s)).natDegree = Bhat.natDegree := by
        rw [hBCdeg, hBdeg]
      have hargs : Polynomial.resultant (toQ f) Bhat
          (((toQ f).map (evalCHom s)).natDegree) ((Bhat.map (evalCHom s)).natDegree) = Res := by
        rw [hRes, hdegeq1, hdegeq2]
      have hkey := Polynomial.resultant_map_map (toQ f) Bhat
        (((toQ f).map (evalCHom s)).natDegree) ((Bhat.map (evalCHom s)).natDegree) (evalCHom s)
      rw [hargs] at hkey
      have hev2 : (Res.map (Rat.castHom ℂ)).eval s = evalCHom s Res := by
        rw [Polynomial.eval_map, hRes, evalCHom]
        rfl
      rw [hev2]
      exact hkey.symm.trans hzero
    have hmapzero := polynomial_eq_zero_of_eventually hev
    exact Polynomial.map_eq_zero_iff (Rat.castHom ℂ).injective |>.mp hmapzero
  -- and now the contradiction with irreducibility over `ℚ(X)`
  have hφKinj : Function.Injective (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) :=
    IsFractionRing.injective (Polynomial ℚ) (FractionRing (Polynomial ℚ))
  have hfKdeg : ((toQ f).map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).natDegree = n := by
    rw [Polynomial.natDegree_map_eq_of_injective hφKinj, hfQdeg]
  have hBKdeg : (Bhat.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).natDegree = d := by
    rw [Polynomial.natDegree_map_eq_of_injective hφKinj, hBdeg]
  have hdegeqK1 : ((toQ f).map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).natDegree
      = (toQ f).natDegree := by rw [hfKdeg, hfQdeg]
  have hdegeqK2 : (Bhat.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).natDegree
      = Bhat.natDegree := by rw [hBKdeg, hBdeg]
  have hargsK : Polynomial.resultant (toQ f) Bhat
      (((toQ f).map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).natDegree)
      ((Bhat.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).natDegree) = Res := by
    rw [hRes, hdegeqK1, hdegeqK2]
  have hkeyK := Polynomial.resultant_map_map (toQ f) Bhat
    (((toQ f).map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).natDegree)
    ((Bhat.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))).natDegree)
    (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
  rw [hargsK] at hkeyK
  have hResK : Polynomial.resultant ((toQ f).map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))))
      (Bhat.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))) = 0 := by
    rw [hkeyK, hResZero, map_zero]
  have hncopK := (Polynomial.resultant_eq_zero_iff.mp hResK).2
  have hdvdK : (toQ f).map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ)))
      ∣ Bhat.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) := by
    by_contra hnd
    exact hncopK ((hirr.coprime_iff_not_dvd).mpr hnd)
  have hBKne : Bhat.map (algebraMap (Polynomial ℚ) (FractionRing (Polynomial ℚ))) ≠ 0 := by
    intro h
    rw [h] at hBKdeg
    simp only [Polynomial.natDegree_zero] at hBKdeg
    omega
  have hle := Polynomial.natDegree_le_of_dvd hdvdK hBKne
  rw [hfKdeg, hBKdeg] at hle
  omega

end GaloisForLFunctions.HTGeometry.HilbertIrreducibility
