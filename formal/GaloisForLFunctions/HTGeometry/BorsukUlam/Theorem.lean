import GaloisForLFunctions.HTGeometry.BorsukUlam.Realization
import GaloisForLFunctions.HTGeometry.BorsukUlam.Tucker
import Mathlib.Topology.UniformSpace.HeineCantor
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Group.BallSphere

/-!
# The Borsuk–Ulam theorem

Every continuous map from the `n`-sphere to `ℝⁿ` identifies a pair of antipodal points.

The proof combines Tucker's lemma with the iterated barycentric subdivisions of the
cross-polytope: an odd nonvanishing map produces an antisymmetric labelling by
`{±1, …, ±n}` (the index of the largest coordinate, with its sign), a complementary edge of a
sufficiently fine subdivision then exhibits two nearby points whose labels disagree in a
coordinate where both are large, contradicting uniform continuity.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.BorsukUlam

open Finset Metric

section Coordinates

variable {m : ℕ}

theorem abs_coord_le_norm (z : EuclideanSpace ℝ (Fin m)) (i : Fin m) : |z i| ≤ ‖z‖ := by
  have h1 : ‖z‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := EuclideanSpace.norm_sq_eq z
  have h2 : ‖z i‖ ^ 2 ≤ ∑ j, ‖z j‖ ^ 2 :=
    Finset.single_le_sum (f := fun j => ‖z j‖ ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h3 : |z i| ^ 2 ≤ ‖z‖ ^ 2 := by
    rw [h1]
    simpa [Real.norm_eq_abs] using h2
  nlinarith [abs_nonneg (z i), norm_nonneg z]

theorem norm_le_card_mul_max (hm : 1 ≤ m) (z : EuclideanSpace ℝ (Fin m)) (i : Fin m)
    (hi : ∀ j, |z j| ≤ |z i|) : ‖z‖ ≤ m * |z i| := by
  have h1 : ‖z‖ ^ 2 = ∑ j, ‖z j‖ ^ 2 := EuclideanSpace.norm_sq_eq z
  have h2 : ∑ j, ‖z j‖ ^ 2 ≤ ∑ _j : Fin m, |z i| ^ 2 := by
    refine Finset.sum_le_sum (fun j _ => ?_)
    rw [Real.norm_eq_abs]
    nlinarith [abs_nonneg (z j), hi j]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have habs : 0 ≤ |z i| := abs_nonneg _
  have h5 : ‖z‖ ^ 2 ≤ (m : ℝ) * |z i| ^ 2 := by rw [h1]; exact h2
  have hmm : (m : ℝ) * |z i| ^ 2 ≤ ((m : ℝ) * |z i|) ^ 2 := by nlinarith [sq_nonneg (|z i|)]
  have hprod : 0 ≤ (m : ℝ) * |z i| := mul_nonneg (by linarith) habs
  by_contra hcon
  push Not at hcon
  nlinarith [norm_nonneg z]

end Coordinates

section Ell1

variable {n : ℕ}

/-- The ℓ¹-unit sphere of `ℝ^{n+1}`. -/
def ell1Sphere (n : ℕ) : Set (EuclideanSpace ℝ (Fin (n + 1))) := {y | ∑ i, |y i| = 1}

theorem mem_ell1Sphere {y : EuclideanSpace ℝ (Fin (n + 1))} :
    y ∈ ell1Sphere n ↔ ∑ i, |y i| = 1 := Iff.rfl

theorem continuous_ell1 : Continuous (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, |y i|) := by
  refine continuous_finset_sum _ (fun i _ => ?_)
  exact (continuous_abs.comp (EuclideanSpace.proj i).continuous)

theorem ell1Sphere_isClosed : IsClosed (ell1Sphere n) := by
  have : ell1Sphere n = (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ∑ i, |y i|) ⁻¹' {1} := rfl
  rw [this]
  exact IsClosed.preimage continuous_ell1 isClosed_singleton

theorem norm_le_one_of_ell1 {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ ell1Sphere n) :
    ‖y‖ ≤ 1 := by
  have hsum : ∑ i, |y i| = 1 := hy
  have hle : ∀ i, |y i| ≤ 1 := by
    intro i
    have := Finset.single_le_sum (f := fun j => |y j|) (fun j _ => abs_nonneg _) (Finset.mem_univ i)
    rw [hsum] at this
    exact this
  have hsq : ‖y‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖y i‖ ^ 2 ≤ ∑ i, |y i| := by
          refine Finset.sum_le_sum (fun i _ => ?_)
          rw [Real.norm_eq_abs]
          nlinarith [abs_nonneg (y i), hle i]
      _ = 1 := hsum
  nlinarith [norm_nonneg y]

theorem ell1Sphere_isCompact : IsCompact (ell1Sphere n) := by
  refine IsCompact.of_isClosed_subset (isCompact_closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)
    ell1Sphere_isClosed ?_
  intro y hy
  rw [mem_closedBall, dist_zero_right]
  exact norm_le_one_of_ell1 hy

theorem ell1Sphere_ne_zero {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ ell1Sphere n) :
    y ≠ 0 := by
  intro hcon
  have hsum : ∑ i, |y i| = 1 := hy
  rw [hcon] at hsum
  simp at hsum

theorem ell1Sphere_neg {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ∈ ell1Sphere n) :
    -y ∈ ell1Sphere n := by
  have hsum : ∑ i, |y i| = 1 := hy
  show ∑ i, |(-y) i| = 1
  rw [← hsum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [PiLp.neg_apply, abs_neg]

/-- Radial projection to the unit sphere. -/
noncomputable def nrm (y : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1)) :=
  ‖y‖⁻¹ • y

theorem nrm_mem_sphere {y : EuclideanSpace ℝ (Fin (n + 1))} (hy : y ≠ 0) :
    nrm y ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  rw [mem_sphere_zero_iff_norm, nrm, norm_smul, norm_inv, norm_norm]
  field_simp

theorem nrm_neg (y : EuclideanSpace ℝ (Fin (n + 1))) : nrm (-y) = - nrm y := by
  rw [nrm, nrm, norm_neg, smul_neg]

theorem continuousOn_nrm : ContinuousOn (nrm : EuclideanSpace ℝ (Fin (n + 1)) → _)
    (ell1Sphere n) := by
  have h1 : ContinuousOn (fun y : EuclideanSpace ℝ (Fin (n + 1)) => ‖y‖⁻¹) (ell1Sphere n) := by
    refine ContinuousOn.inv₀ continuous_norm.continuousOn ?_
    intro y hy
    exact norm_ne_zero_iff.mpr (ell1Sphere_ne_zero hy)
  exact h1.smul continuousOn_id

end Ell1

section Main

/-- There is no odd continuous nonvanishing map from the `n`-sphere to `ℝⁿ` when `n ≥ 1`. -/
theorem no_odd_nonvanishing (n : ℕ) (hn : 1 ≤ n)
    (g : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hgc : ContinuousOn g (sphere 0 1))
    (hodd : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, g (-x) = - g x)
    (hgnz : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, g x ≠ 0) : False := by
  classical
  -- the composite with radial projection, on the ℓ¹-sphere
  set G : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) := fun y => g (nrm y) with hGdef
  have hnrmmem : ∀ y ∈ ell1Sphere n, nrm y ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 :=
    fun y hy => nrm_mem_sphere (ell1Sphere_ne_zero hy)
  have hGcont : ContinuousOn G (ell1Sphere n) :=
    ContinuousOn.comp hgc continuousOn_nrm hnrmmem
  have hGnz : ∀ y ∈ ell1Sphere n, G y ≠ 0 := fun y hy => hgnz _ (hnrmmem y hy)
  have hGodd : ∀ y ∈ ell1Sphere n, G (-y) = - G y := by
    intro y hy
    show g (nrm (-y)) = - g (nrm y)
    rw [nrm_neg]
    exact hodd _ (hnrmmem y hy)
  -- a positive lower bound for ‖G‖ on the ℓ¹-sphere
  have hne : (ell1Sphere n).Nonempty := by
    refine ⟨EuclideanSpace.single 0 1, ?_⟩
    show ∑ i, |EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) i| = 1
    calc ∑ i, |EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ) i|
        = ∑ i : Fin (n + 1), (if i = 0 then (1 : ℝ) else 0) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [EuclideanSpace.single_apply]
          by_cases h : i = 0 <;> simp [h]
      _ = 1 := by simp
  obtain ⟨y₀, hy₀, hmin⟩ := ell1Sphere_isCompact.exists_isMinOn hne
    (continuous_norm.comp_continuousOn hGcont)
  set ε := ‖G y₀‖ with hεdef
  have hεpos : 0 < ε := norm_pos_iff.mpr (hGnz y₀ hy₀)
  have hεle : ∀ y ∈ ell1Sphere n, ε ≤ ‖G y‖ := fun y hy => hmin hy
  -- uniform continuity
  have hunif : UniformContinuousOn G (ell1Sphere n) :=
    ell1Sphere_isCompact.uniformContinuousOn_of_continuous hGcont
  rw [Metric.uniformContinuousOn_iff] at hunif
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨δ, hδpos, hδ⟩ := hunif (2 * ε / n) (by positivity)
  -- a fine subdivision
  have hq : |(n : ℝ) / (n + 1)| < 1 := by
    rw [abs_of_nonneg (by positivity)]
    rw [div_lt_one (by positivity)]
    linarith
  have htend := tendsto_pow_atTop_nhds_zero_of_abs_lt_one hq
  have htend2 : Filter.Tendsto (fun m : ℕ => ((n : ℝ) / (n + 1)) ^ m * 2) Filter.atTop
      (nhds 0) := by
    have := htend.mul_const (2 : ℝ)
    simpa using this
  obtain ⟨m, hm⟩ : ∃ m : ℕ, ((n : ℝ) / (n + 1)) ^ m * 2 < δ := by
    have := (Metric.tendsto_atTop.mp htend2) δ hδpos
    obtain ⟨M, hM⟩ := this
    refine ⟨M, ?_⟩
    have := hM M (le_refl M)
    rw [Real.dist_eq, sub_zero] at this
    exact lt_of_abs_lt this
  set Geo := GeoFlag.tower (crossGeo n) m with hGeodef
  have hmeshlt : Geo.mesh < δ := by
    rw [hGeodef, GeoFlag.tower_mesh]
    exact hm
  have hφmem : ∀ v : Geo.K.V, Geo.φ v ∈ ell1Sphere n := fun v => Geo.φ_l1 v
  -- the index of a largest coordinate
  obtain ⟨F, hF⟩ : ∃ F : (Fin n → ℝ) → Fin n, ∀ (w : Fin n → ℝ) (j : Fin n), w j ≤ w (F w) := by
    have hex : ∀ w : Fin n → ℝ, ∃ i, ∀ j, w j ≤ w i := by
      intro w
      obtain ⟨i, -, hi⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin n)) w
        ⟨⟨0, hn⟩, Finset.mem_univ _⟩
      exact ⟨i, fun j => hi j (Finset.mem_univ j)⟩
    choose F hF using hex
    exact ⟨F, hF⟩
  set idxOf : EuclideanSpace ℝ (Fin n) → Fin n := fun z => F (fun j => |z j|) with hidxdef
  have hidxmax : ∀ (z : EuclideanSpace ℝ (Fin n)) (j : Fin n), |z j| ≤ |z (idxOf z)| :=
    fun z j => hF (fun j => |z j|) j
  have hidxneg : ∀ z : EuclideanSpace ℝ (Fin n), idxOf (-z) = idxOf z := by
    intro z
    show F (fun j => |(-z) j|) = F (fun j => |z j|)
    congr 1
    funext j
    rw [PiLp.neg_apply, abs_neg]
  have hmaxpos : ∀ z : EuclideanSpace ℝ (Fin n), z ≠ 0 → 0 < |z (idxOf z)| := by
    intro z hz
    rcases lt_or_eq_of_le (abs_nonneg (z (idxOf z))) with h | h
    · exact h
    · exfalso
      apply hz
      ext j
      have := hidxmax z j
      rw [← h] at this
      have habs : |z j| = 0 := le_antisymm this (abs_nonneg _)
      rw [PiLp.zero_apply]
      exact abs_eq_zero.mp habs
  -- the labelling
  set lab : Geo.K.V → ℤ := fun v =>
    if 0 < (G (Geo.φ v)) (idxOf (G (Geo.φ v))) then ((idxOf (G (Geo.φ v)) : ℕ) + 1 : ℤ)
    else -(((idxOf (G (Geo.φ v)) : ℕ) + 1 : ℤ)) with hlabdef
  have habs_lab : ∀ v, |lab v| = ((idxOf (G (Geo.φ v)) : ℕ) + 1 : ℤ) := by
    intro v
    simp only [hlabdef]
    by_cases h : 0 < (G (Geo.φ v)) (idxOf (G (Geo.φ v)))
    · rw [if_pos h, abs_of_nonneg (by positivity)]
    · rw [if_neg h, abs_neg, abs_of_nonneg (by positivity)]
  have hnzlab : ∀ v, lab v ≠ 0 := by
    intro v
    intro hcon
    have := habs_lab v
    rw [hcon] at this
    simp at this
    omega
  have hboundlab : ∀ v, |lab v| ≤ (n : ℤ) := by
    intro v
    rw [habs_lab v]
    have := (idxOf (G (Geo.φ v))).isLt
    omega
  have hantilab : ∀ v, lab (Geo.K.neg v) = -(lab v) := by
    intro v
    have hφ : Geo.φ (Geo.K.neg v) = - Geo.φ v := Geo.φ_neg v
    have hG : G (Geo.φ (Geo.K.neg v)) = - G (Geo.φ v) := by
      rw [hφ]
      exact hGodd _ (hφmem v)
    have hidx : idxOf (G (Geo.φ (Geo.K.neg v))) = idxOf (G (Geo.φ v)) := by
      rw [hG, hidxneg]
    have hcoord : (G (Geo.φ (Geo.K.neg v))) (idxOf (G (Geo.φ v))) =
        -((G (Geo.φ v)) (idxOf (G (Geo.φ v)))) := by
      rw [hG, PiLp.neg_apply]
    have hpos : 0 < |(G (Geo.φ v)) (idxOf (G (Geo.φ v)))| :=
      hmaxpos _ (hGnz _ (hφmem v))
    simp only [hlabdef]
    rw [hidx, hcoord]
    by_cases h : 0 < (G (Geo.φ v)) (idxOf (G (Geo.φ v)))
    · rw [if_pos h, if_neg (by linarith)]
    · have hneg : (G (Geo.φ v)) (idxOf (G (Geo.φ v))) < 0 := by
        rcases lt_trichotomy ((G (Geo.φ v)) (idxOf (G (Geo.φ v)))) 0 with hh | hh | hh
        · exact hh
        · rw [hh] at hpos; simp at hpos
        · exact absurd hh h
      rw [if_neg h, if_pos (by linarith)]
      ring
  -- Tucker's lemma produces a complementary edge
  obtain ⟨σ, hσ, u, hu, v, hv, hsum⟩ :=
    FlagComplex.tucker Geo.K lab hn hnzlab hboundlab hantilab
  -- the two endpoints have large opposite coordinates
  set zu := G (Geo.φ u) with hzu
  set zv := G (Geo.φ v) with hzv
  have hiuv : idxOf zu = idxOf zv := by
    have h1 : |lab u| = |lab v| := by
      rw [show lab u = -(lab v) by omega, abs_neg]
    rw [habs_lab u, habs_lab v, ← hzu, ← hzv] at h1
    have : ((idxOf zu : ℕ) : ℤ) = ((idxOf zv : ℕ) : ℤ) := by omega
    exact Fin.ext (by exact_mod_cast this)
  have hzunz : zu ≠ 0 := hGnz _ (hφmem u)
  have hzvnz : zv ≠ 0 := hGnz _ (hφmem v)
  have hposu : 0 < |zu (idxOf zu)| := hmaxpos _ hzunz
  have hposv : 0 < |zv (idxOf zv)| := hmaxpos _ hzvnz
  have hlargeu : ε / n ≤ |zu (idxOf zu)| := by
    have h1 : ‖zu‖ ≤ n * |zu (idxOf zu)| := norm_le_card_mul_max hn _ _ (hidxmax _)
    have h2 : ε ≤ ‖zu‖ := hεle _ (hφmem u)
    rw [div_le_iff₀ hnR]
    linarith
  have hlargev : ε / n ≤ |zv (idxOf zv)| := by
    have h1 : ‖zv‖ ≤ n * |zv (idxOf zv)| := norm_le_card_mul_max hn _ _ (hidxmax _)
    have h2 : ε ≤ ‖zv‖ := hεle _ (hφmem v)
    rw [div_le_iff₀ hnR]
    linarith
  have hlabu : lab u = if 0 < zu (idxOf zu) then ((idxOf zu : ℕ) + 1 : ℤ)
      else -(((idxOf zu : ℕ) + 1 : ℤ)) := rfl
  have hlabv : lab v = if 0 < zv (idxOf zv) then ((idxOf zv : ℕ) + 1 : ℤ)
      else -(((idxOf zv : ℕ) + 1 : ℤ)) := rfl
  have hsigns : (0 < zu (idxOf zu) ∧ zv (idxOf zv) < 0) ∨
      (zu (idxOf zu) < 0 ∧ 0 < zv (idxOf zv)) := by
    by_cases h : 0 < zu (idxOf zu)
    · refine Or.inl ⟨h, ?_⟩
      by_contra hcon
      push Not at hcon
      have hpos2 : 0 < zv (idxOf zv) := by
        rcases lt_trichotomy (zv (idxOf zv)) 0 with hh | hh | hh
        · exact absurd hh (by linarith)
        · exfalso
          rw [hh] at hposv
          simp at hposv
        · exact hh
      rw [hlabu, if_pos h] at hsum
      rw [hlabv, if_pos hpos2] at hsum
      omega
    · have hneg : zu (idxOf zu) < 0 := by
        rcases lt_trichotomy (zu (idxOf zu)) 0 with hh | hh | hh
        · exact hh
        · exfalso
          rw [hh] at hposu
          simp at hposu
        · exact absurd hh h
      refine Or.inr ⟨hneg, ?_⟩
      by_contra hcon
      push Not at hcon
      have hneg2 : zv (idxOf zv) < 0 := by
        rcases lt_trichotomy (zv (idxOf zv)) 0 with hh | hh | hh
        · exact hh
        · exfalso
          rw [hh] at hposv
          simp at hposv
        · exact absurd hh (by linarith)
      rw [hlabu, if_neg h] at hsum
      rw [hlabv, if_neg (not_lt.mpr (le_of_lt hneg2))] at hsum
      omega
  rw [← hiuv] at hposv hlargev hsigns
  -- the two points are close, so their images are close
  have hclose : dist (Geo.φ u) (Geo.φ v) < δ := by
    have hb := Geo.mesh_bound σ hσ u hu v hv
    rw [dist_eq_norm]
    linarith
  have hGclose : dist zu zv < 2 * ε / n :=
    hδ (Geo.φ u) (hφmem u) (Geo.φ v) (hφmem v) hclose
  have hcoordclose : |zu (idxOf zu) - zv (idxOf zu)| < 2 * ε / n := by
    have h1 : |(zu - zv) (idxOf zu)| ≤ ‖zu - zv‖ := abs_coord_le_norm _ _
    rw [PiLp.sub_apply] at h1
    rw [dist_eq_norm] at hGclose
    linarith
  have hbig : 2 * ε / n ≤ |zu (idxOf zu) - zv (idxOf zu)| := by
    rcases hsigns with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [abs_of_pos (by linarith)]
      rw [abs_of_pos h1] at hlargeu
      rw [abs_of_neg h2] at hlargev
      have : 2 * ε / n = ε / n + ε / n := by ring
      linarith
    · rw [abs_of_neg (by linarith)]
      rw [abs_of_neg h1] at hlargeu
      rw [abs_of_pos h2] at hlargev
      have : 2 * ε / n = ε / n + ε / n := by ring
      linarith
  linarith

/-- **The Borsuk–Ulam theorem.**  Every continuous map from the `n`-sphere to `ℝⁿ` takes the same
value at some pair of antipodal points. -/
theorem borsuk_ulam {n : ℕ} (f : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hf : ContinuousOn f (sphere 0 1)) :
    ∃ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, f x = f (-x) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · refine ⟨EuclideanSpace.single 0 1, ?_, ?_⟩
    · rw [mem_sphere_zero_iff_norm, EuclideanSpace.norm_single]
      simp
    · refine PiLp.ext (fun i => ?_)
      exact Fin.elim0 i
  · by_contra hcon
    push Not at hcon
    have hnegmem : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1,
        -x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
      intro x hx
      rw [mem_sphere_zero_iff_norm, norm_neg]
      exact mem_sphere_zero_iff_norm.mp hx
    refine no_odd_nonvanishing n hn (fun x => f x - f (-x)) ?_ ?_ ?_
    · refine hf.sub ?_
      refine hf.comp continuous_neg.continuousOn ?_
      exact hnegmem
    · intro x hx
      rw [neg_neg]
      abel
    · intro x hx hzero
      exact hcon x hx (by
        have := sub_eq_zero.mp hzero
        exact this)

/-- There is no continuous odd map from the `n`-sphere to the `(n-1)`-sphere, `n ≥ 1`. -/
theorem no_odd_map_to_smaller_sphere {n : ℕ} (hn : 1 ≤ n)
    (h : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n))
    (hc : ContinuousOn h (sphere 0 1))
    (hodd : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, h (-x) = - h x)
    (hmaps : ∀ x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, ‖h x‖ = 1) : False := by
  refine no_odd_nonvanishing n hn h hc hodd (fun x hx hzero => ?_)
  have := hmaps x hx
  rw [hzero, norm_zero] at this
  exact zero_ne_one this

/-- Borsuk–Ulam for a map defined on the sphere as a subtype. -/
theorem borsuk_ulam_sphere {n : ℕ}
    (f : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 → EuclideanSpace ℝ (Fin n))
    (hf : Continuous f) :
    ∃ x : sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1, f x = f (-x) := by
  classical
  set F : EuclideanSpace ℝ (Fin (n + 1)) → EuclideanSpace ℝ (Fin n) :=
    fun x => if hx : x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 then f ⟨x, hx⟩ else 0
    with hFdef
  have hFc : ContinuousOn F (sphere 0 1) := by
    rw [continuousOn_iff_continuous_restrict]
    have : (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1).restrict F = f := by
      funext x
      simp only [Set.restrict_apply, hFdef, dif_pos x.2]
    rw [this]
    exact hf
  obtain ⟨x, hx, hxeq⟩ := borsuk_ulam F hFc
  have hnegmem : -x ∈ sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
    rw [mem_sphere_zero_iff_norm, norm_neg]
    exact mem_sphere_zero_iff_norm.mp hx
  refine ⟨⟨x, hx⟩, ?_⟩
  have h1 : F x = f ⟨x, hx⟩ := by simp only [hFdef, dif_pos hx]
  have h2 : F (-x) = f ⟨-x, hnegmem⟩ := by simp only [hFdef, dif_pos hnegmem]
  rw [h1, h2] at hxeq
  rw [hxeq]
  congr 1

end Main

end GaloisForLFunctions.BorsukUlam
