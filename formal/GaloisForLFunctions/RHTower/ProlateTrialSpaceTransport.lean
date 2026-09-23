import GaloisForLFunctions.RHTower.ProlateHermiteTrialSpace
import GaloisForLFunctions.RHTower.ProlateRelativeTrialBound

/-!
# Transporting the Hermite trial space into the band `L²` space

The rescaled Hermite family is smooth and, at even rungs, even; so its band classes span a
subspace of the aperture `L²` space on which the relative trial bound applies.  Combining the
liveness of the trial space with the dimension count gives, at every large bandwidth, at least
`j+1` independent even joint band/prolate modes with separation constant below the top rung.
-/

open Filter Topology Set MeasureTheory Finset GaloisForLFunctions.HTGeometry

noncomputable section

namespace RHTower

variable {j : ℕ}

theorem contDiff_polyEval (p : Polynomial ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun x : ℝ => p.eval x) := by
  have h := Polynomial.contDiff_aeval (𝕜 := ℝ) p (((⊤ : ℕ∞) : WithTop ℕ∞))
  have heq : (fun x : ℝ => Polynomial.aeval x p) = fun x : ℝ => p.eval x := by
    funext x
    simp
  rwa [heq] at h

theorem contDiff_hermiteFun (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hermiteFun n) := by
  obtain ⟨p, hp⟩ := exists_poly_hermiteFun n
  have heq : hermiteFun n = fun x : ℝ => p.eval x * Real.exp (-(1 / 2 * x ^ (2 : ℕ))) := funext hp
  rw [heq]
  refine (contDiff_polyEval p).mul (Real.contDiff_exp.comp ?_)
  exact (contDiff_const.mul (contDiff_id.pow 2)).neg

theorem contDiff_prolateHermiteTrial (c : ℝ) (n : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (prolateHermiteTrial c n) := by
  rw [prolateHermiteTrial_eq]
  exact (contDiff_hermiteFun n).comp (contDiff_const.mul contDiff_id)

theorem even_prolateHermiteTrial (c : ℝ) {n : ℕ} (hn : Even n) :
    Function.Even (prolateHermiteTrial c n) := by
  intro x
  show hermiteFun n (Real.sqrt c * -x) = hermiteFun n (Real.sqrt c * x)
  rw [show Real.sqrt c * -x = -(Real.sqrt c * x) by ring, even_hermiteFun hn]

theorem contDiff_hermiteTrialVector (ν : Fin (j + 1) → ℕ) (a : Fin (j + 1) → ℝ) (c : ℝ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hermiteTrialVector ν a c) := by
  rw [hermiteTrialVector_eq]
  exact ContDiff.sum fun i _ => contDiff_const.mul (contDiff_prolateHermiteTrial c (ν i))

theorem even_hermiteTrialVector {ν : Fin (j + 1) → ℕ} (hν : ∀ i, Even (ν i))
    (a : Fin (j + 1) → ℝ) (c : ℝ) : Function.Even (hermiteTrialVector ν a c) := by
  intro x
  rw [hermiteTrialVector, hermiteTrialVector]
  exact Finset.sum_congr rfl fun i _ => by rw [even_prolateHermiteTrial c (hν i)]

theorem continuous_hermiteTrialVector (ν : Fin (j + 1) → ℕ) (a : Fin (j + 1) → ℝ) (c : ℝ) :
    Continuous (hermiteTrialVector ν a c) := (contDiff_hermiteTrialVector ν a c).continuous

/-- The band class of a trial vector is the corresponding combination of the basis band classes. -/
theorem bandClass_hermiteTrialVector (ν : Fin (j + 1) → ℕ) (a : Fin (j + 1) → ℝ) (c : ℝ) :
    GaloisForLFunctions.RHTower.bandClass (hermiteTrialVector ν a c)
        (continuous_hermiteTrialVector ν a c)
      = ∑ i, a i • GaloisForLFunctions.RHTower.bandClass (prolateHermiteTrial c (ν i))
          (continuous_prolateHermiteTrial c (ν i)) :=
  GaloisForLFunctions.RHTower.bandClass_finsetSum Finset.univ a
    (fun i => prolateHermiteTrial c (ν i))
    (fun i => continuous_prolateHermiteTrial c (ν i)) _

/-- The band-class span of the rescaled Hermite trial family. -/
def hermiteTrialSpan (ν : Fin (j + 1) → ℕ) (c : ℝ) :
    Submodule ℝ (GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1) :=
  Submodule.span ℝ (Set.range fun i => GaloisForLFunctions.RHTower.bandClass
    (prolateHermiteTrial c (ν i)) (continuous_prolateHermiteTrial c (ν i)))

/-- **The trial span avoids the orthogonal complement of the high-mode span.**  At every large
bandwidth the rescaled Hermite trial space meets the orthogonal complement of the span of the joint
even modes with separation constant below `Λ+ε` only in zero. -/
theorem eventually_disjoint_hermiteTrialSpan
    (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) (hν : ∀ i, Even (ν i))
    {Λ ε : ℝ} (hε : 0 < ε) (hΛ : ∀ i, 2 * (ν i : ℝ) + 1 ≤ Λ) :
    ∀ᶠ c in atTop, Disjoint (hermiteTrialSpan ν c) (highProlateSpan c ((Λ + ε) * c))ᗮ := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_hermiteTrial_rayleigh_gt ν hinj hε hΛ]
    with c hcpos hlive
  refine disjoint_trialSpace_orthogonal_highProlateSpan hcpos _ ?_
  intro w hw hwne
  obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw
  have hane : ∃ i, a i ≠ 0 := by
    by_contra hcon
    rw [not_exists] at hcon
    apply hwne
    rw [← ha]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [not_not.1 (hcon i), zero_smul]
  refine ⟨hermiteTrialVector ν a c, contDiff_hermiteTrialVector ν a c,
    even_hermiteTrialVector hν a c, ((bandClass_hermiteTrialVector ν a c).trans ha).symm,
    hlive a hane⟩

/-- The trial band classes are linearly independent at every large bandwidth. -/
theorem eventually_linearIndependent_hermiteTrialBasis
    (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) :
    ∀ᶠ c in atTop, LinearIndependent ℝ (fun i => GaloisForLFunctions.RHTower.bandClass
      (prolateHermiteTrial c (ν i)) (continuous_prolateHermiteTrial c (ν i))) := by
  filter_upwards [eventually_gt_atTop (0 : ℝ), eventually_hermiteTrial_norm_pos ν hinj]
    with c hcpos hnorm
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  by_contra hgi
  have hpos := hnorm g ⟨i, hgi⟩
  have hzero : GaloisForLFunctions.RHTower.bandClass (hermiteTrialVector ν g c)
      (continuous_hermiteTrialVector ν g c) = 0 := by
    rw [bandClass_hermiteTrialVector]
    exact hg
  have heqOn := GaloisForLFunctions.RHTower.eqOn_of_bandClass_eq
    (continuous_hermiteTrialVector ν g c) continuous_const
    (hzero.trans (GaloisForLFunctions.RHTower.bandClass_zero continuous_const).symm)
  have hvan : (∫ x in (-1 : ℝ)..1,
      hermiteTrialVector ν g c x * hermiteTrialVector ν g c x) = 0 := by
    have hcongr : (∫ x in (-1 : ℝ)..1,
        hermiteTrialVector ν g c x * hermiteTrialVector ν g c x)
        = ∫ _ in (-1 : ℝ)..1, (0 : ℝ) := by
      refine intervalIntegral.integral_congr fun x hx => ?_
      have hx' : x ∈ Set.Icc (-1 : ℝ) 1 := by
        rwa [Set.uIcc_of_le (by norm_num : (-1 : ℝ) ≤ 1)] at hx
      rw [heqOn x hx']
      ring
    rw [hcongr]
    simp
  linarith [hpos, hvan]

/-- **The high-mode span is at least as large as the trial space.**  At every large bandwidth the
span of the joint even modes with separation constant below `Λ+ε` has rank at least `j+1`. -/
theorem eventually_rank_hermiteTrialSpan_eq
    (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) :
    ∀ᶠ c in atTop, Module.rank ℝ (hermiteTrialSpan ν c) = ((j : Cardinal) + 1) := by
  filter_upwards [eventually_linearIndependent_hermiteTrialBasis ν hinj] with c hli
  rw [hermiteTrialSpan, rank_span hli, Cardinal.mk_range_eq _ hli.injective]
  simp

/-- **The upper half of the differential ordering.**  At every large bandwidth, the span of the
joint even band/prolate modes with separation constant below `Λ+ε` has rank at least `j+1`: the
rescaled Hermite trial space of that many distinct rungs injects into it under orthogonal
projection. -/
theorem eventually_rank_highProlateSpan_ge
    (ν : Fin (j + 1) → ℕ) (hinj : Function.Injective ν) (hν : ∀ i, Even (ν i))
    {Λ ε : ℝ} (hε : 0 < ε) (hΛ : ∀ i, 2 * (ν i : ℝ) + 1 ≤ Λ) :
    ∀ᶠ c in atTop, ∀ _ : (highProlateSpan c ((Λ + ε) * c)).HasOrthogonalProjection,
      ((j : Cardinal) + 1) ≤ Module.rank ℝ (highProlateSpan c ((Λ + ε) * c)) := by
  filter_upwards [eventually_disjoint_hermiteTrialSpan ν hinj hν hε hΛ,
    eventually_rank_hermiteTrialSpan_eq ν hinj] with c hdisj hrank
  intro hinst
  haveI := hinst
  have hle := rank_le_of_disjoint_orthogonal (hermiteTrialSpan ν c) hdisj
  rwa [hrank] at hle

/-- **The even sector.**  Taking the first `j+1` even rungs, at every large bandwidth there are at
least `j+1` independent joint even modes with separation constant below `4j+1+ε`. -/
theorem eventually_rank_highProlateSpan_even_ge (j : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ c in atTop,
      ∀ _ : (highProlateSpan c ((4 * (j : ℝ) + 1 + ε) * c)).HasOrthogonalProjection,
        ((j : Cardinal) + 1)
          ≤ Module.rank ℝ (highProlateSpan c ((4 * (j : ℝ) + 1 + ε) * c)) := by
  have hinj : Function.Injective (fun i : Fin (j + 1) => 2 * (i : ℕ)) := by
    intro i k h
    simp only at h
    exact Fin.ext (by omega)
  have hν : ∀ i : Fin (j + 1), Even (2 * (i : ℕ)) := fun i => ⟨(i : ℕ), by ring⟩
  have hΛ : ∀ i : Fin (j + 1), 2 * ((2 * (i : ℕ) : ℕ) : ℝ) + 1 ≤ 4 * (j : ℝ) + 1 := by
    intro i
    have hi : ((i : ℕ) : ℝ) ≤ (j : ℝ) := by
      have := Nat.lt_succ_iff.1 i.isLt
      exact_mod_cast this
    push_cast
    linarith
  exact eventually_rank_highProlateSpan_ge (fun i : Fin (j + 1) => 2 * (i : ℕ)) hinj hν hε hΛ

end RHTower
