import GaloisForLFunctions.MultiplicativePositivityGeometry.AbelianZeroMass
import GaloisForLFunctions.MultiplicativePositivityGeometry.FiniteBoundaryDivisors
import GaloisForLFunctions.MultiplicativePositivityGeometry.BoundaryRegularity
import GaloisForLFunctions.MultiplicativePositivityGeometry.IntegralRealization
import Mathlib.Analysis.Real.Cardinality

/-!
# Summable positive-definite configurations and rank-`r` boundary profiles

* **Bochner positivity in `ℓ¹`** (`tsum_nonneg_of_gram`, `IsEvenPosDef.tsum_mul_cos_nonneg`). On any
  abelian group `Γ`, an absolutely summable even positive-definite `φ` has `Σ_γ φ(γ) cos θ(γ) ≥ 0`
  for every additive `θ : Γ →+ ℝ`. The Gram forms with coefficients `cos θ`, `sin θ` over a Følner
  set `F` give `Σ_p φ(p) cos θ(p) · #{y ∈ F : y + p ∈ F} ≥ 0`; the counts are `≥ (1 − ε)|F|` on a
  finite set carrying all but `ε` of the mass.
* **Realization** (`summable_isBoundaryDivisor`, `summable_integral`). For such `φ` and additive
  heights `h : Γ →+ ℝ` the pushforward `D_h(u) = Σ_{h(γ) = u} φ(γ)` is the boundary divisor of the
  von Mangoldt weights twisted by `B(t) = Σ_γ φ(γ) cos(t h(γ)) ≥ 0`, and, `B` being bounded, of an
  Euler product `Π_p (1 − p^{−s})^{−m(p)}` with `m(p) ∈ ℕ`. For `Γ = ℝ` every absolutely summable
  even positive-definite function on `ℝ` is realized, whatever its support (dense supports included).
* **Rank-`r` profiles** (APD topic 7). For heights `t ∈ ℝ^r` with `k ↦ ⟨k, t⟩` injective on `ℤ^r`:
  every absolutely summable positive-definite profile on `ℤ^r` is the boundary profile of an
  integral Euler product (`rank_profile_integral`); an integer-valued profile with a unit pole is a
  boundary profile only if any two points of its support are proportional
  (`rank_profile_collapse`): boundary regularity forbids a nonvanishing subgroup of rank `≥ 2`,
  whose image in `ℝ` is dense.
-/

open Finset Filter Topology

namespace GaloisForLFunctions.MultiplicativePositivityGeometry

/-! ### Bochner positivity in `ℓ¹` -/

section Positivity

variable {Γ : Type*} [AddCommGroup Γ]

/-- The Gram form of `φ · cos θ` over a finite set is nonnegative. -/
theorem IsEvenPosDef.sum_sum_cos_nonneg {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (θ : Γ →+ ℝ)
    (F : Finset Γ) : 0 ≤ ∑ x ∈ F, ∑ y ∈ F, φ (x - y) * Real.cos (θ (x - y)) := by
  have h1 := hφ.sum_finset_mul_nonneg F fun x => Real.cos (θ x)
  have h2 := hφ.sum_finset_mul_nonneg F fun x => Real.sin (θ x)
  have e : ∑ x ∈ F, ∑ y ∈ F, φ (x - y) * Real.cos (θ (x - y)) =
      ∑ x ∈ F, ∑ y ∈ F, Real.cos (θ x) * Real.cos (θ y) * φ (x - y) +
        ∑ x ∈ F, ∑ y ∈ F, Real.sin (θ x) * Real.sin (θ y) * φ (x - y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [map_sub, Real.cos_sub]
    ring
  rw [e]
  exact add_nonneg h1 h2

/-- **Bochner positivity in `ℓ¹`, abstract form.** If `|ψ| ≤ |φ|` with `φ` absolutely summable and
every Gram sum `Σ_{x,y ∈ F} ψ(x − y)` over a finite set is nonnegative, then `Σ ψ ≥ 0`: a Følner set
of a finite set carrying all but `ε` of the mass sees each of its points with weight `≥ (1 − ε)|F|`. -/
theorem tsum_nonneg_of_gram {φ ψ : Γ → ℝ} (hs : Summable φ) (hψφ : ∀ γ, |ψ γ| ≤ |φ γ|)
    (hgram : ∀ F : Finset Γ, 0 ≤ ∑ x ∈ F, ∑ y ∈ F, ψ (x - y)) : 0 ≤ ∑' γ, ψ γ := by
  classical
  have habs : Summable fun γ => |φ γ| := hs.abs
  have hψ : Summable ψ := Summable.of_norm_bounded habs fun γ => by
    rw [Real.norm_eq_abs]; exact hψφ γ
  set A := ∑' γ, |φ γ|
  have hA : 0 ≤ A := tsum_nonneg fun γ => abs_nonneg _
  refine le_of_forall_pos_lt_add fun ε hε => ?_
  -- A finite set `S` carrying all but `ε/4` of the mass.
  have ht : Tendsto (fun s : Finset Γ => ∑ b ∈ s, |φ b|) atTop (𝓝 A) := habs.hasSum
  obtain ⟨S, hS⟩ := Metric.tendsto_atTop.mp ht (ε / 4) (by positivity)
  have hSt : ∑' γ, |φ γ| * (if γ ∈ S then 0 else 1) < ε / 4 := by
    have hsplit : ∑' γ, |φ γ| * (if γ ∈ S then 0 else 1) = A - ∑ γ ∈ S, |φ γ| := by
      have hin : ∑' γ, |φ γ| * (if γ ∈ S then 1 else 0) = ∑ γ ∈ S, |φ γ| := by
        rw [tsum_eq_sum (s := S) fun γ hγ => by rw [if_neg hγ, mul_zero]]
        exact Finset.sum_congr rfl fun γ hγ => by rw [if_pos hγ, mul_one]
      have hs1 : Summable fun γ => |φ γ| * (if γ ∈ S then 0 else 1) :=
        Summable.of_nonneg_of_le (fun γ => by split_ifs <;> simp) (fun γ => by
          split_ifs <;> simp) habs
      have hs2 : Summable fun γ => |φ γ| * (if γ ∈ S then 1 else 0) :=
        Summable.of_nonneg_of_le (fun γ => by split_ifs <;> simp) (fun γ => by
          split_ifs <;> simp) habs
      rw [← hin, eq_sub_iff_add_eq, ← Summable.tsum_add hs1 hs2]
      exact tsum_congr fun γ => by split_ifs <;> ring
    rw [hsplit]
    have := hS S le_rfl
    rw [Real.dist_eq] at this
    linarith [(abs_lt.mp this).1]
  -- A Følner set for `S` with growth `1 + ε'`.
  set ε' := ε / (4 * (A + 1))
  have hε' : 0 < ε' := by positivity
  obtain ⟨N, hN1, hgrow⟩ := exists_abFolner_step S hε'
  set F := abFolnerSet S N
  have hF0 : (0 : ℝ) < F.card := by
    exact_mod_cast Finset.card_pos.mpr ⟨0, zero_mem_abFolnerSet S hN1⟩
  set c : Γ → ℝ := fun p => ((F.filter fun y => y + p ∈ F).card : ℝ)
  have hc_le : ∀ p, c p ≤ F.card := fun p => by
    simp only [c]; exact_mod_cast Finset.card_filter_le _ _
  have hc_nonneg : ∀ p, 0 ≤ c p := fun p => Nat.cast_nonneg _
  have hc_S : ∀ p ∈ S, (1 - ε') * F.card ≤ c p := fun p hp => by
    have := card_abShift_mem_ge (N := N) hp
    linarith
  -- The Gram identity: `0 ≤ Σ_p ψ(p) c(p)`.
  set S' : Finset Γ := (F ×ˢ F).image fun q => q.1 - q.2
  have hc_out : ∀ p ∉ S', c p = 0 := fun p hp => by
    simp only [c, Nat.cast_eq_zero, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro y hy hyp
    exact hp (Finset.mem_image.mpr ⟨(y + p, y), Finset.mem_product.mpr ⟨hyp, hy⟩, by simp⟩)
  have hgram : 0 ≤ ∑' p, ψ p * c p := by
    rw [tsum_eq_sum (s := S') fun p hp => by rw [hc_out p hp, mul_zero]]
    have h := sum_sum_ite_sub_eq F S' ψ
    have hall : ∑ x ∈ F, ∑ y ∈ F, (if x - y ∈ S' then ψ (x - y) else 0) =
        ∑ x ∈ F, ∑ y ∈ F, ψ (x - y) :=
      Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun y hy => by
        rw [if_pos (Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩)]
    rw [← h, hall]
    exact hgram F
  -- Compare with `|F| Σ ψ`.
  have hψc : Summable fun p => ψ p * c p :=
    Summable.of_norm_bounded (habs.mul_right (F.card : ℝ)) fun p => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hc_nonneg p)]
      exact mul_le_mul (hψφ p) (hc_le p) (hc_nonneg p) (abs_nonneg _)
  have hdef : Summable fun p => |φ p| * (F.card - c p) :=
    Summable.of_nonneg_of_le (fun p => mul_nonneg (abs_nonneg _) (by linarith [hc_le p]))
      (fun p => mul_le_mul_of_nonneg_left (by linarith [hc_nonneg p]) (abs_nonneg _))
      (habs.mul_right (F.card : ℝ))
  have hbound : ∀ p, |φ p| * (F.card - c p) ≤
      ε' * F.card * |φ p| + F.card * (|φ p| * (if p ∈ S then 0 else 1)) := fun p => by
    by_cases hp : p ∈ S
    · rw [if_pos hp, mul_zero, mul_zero, add_zero]
      have := hc_S p hp
      calc |φ p| * (F.card - c p) ≤ |φ p| * (ε' * F.card) :=
            mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
        _ = ε' * F.card * |φ p| := by ring
    · rw [if_neg hp, mul_one]
      have h1 : |φ p| * (F.card - c p) ≤ |φ p| * F.card :=
        mul_le_mul_of_nonneg_left (by linarith [hc_nonneg p]) (abs_nonneg _)
      have h2 : 0 ≤ ε' * F.card * |φ p| := by positivity
      linarith
  have hsS : Summable fun p => |φ p| * (if p ∈ S then 0 else 1) :=
    Summable.of_nonneg_of_le (fun γ => by split_ifs <;> simp) (fun γ => by split_ifs <;> simp) habs
  have hdefle : ∑' p, |φ p| * (F.card - c p) ≤ ε' * F.card * A + F.card * (ε / 4) := by
    calc ∑' p, |φ p| * (F.card - c p)
        ≤ ∑' p, (ε' * F.card * |φ p| + F.card * (|φ p| * (if p ∈ S then 0 else 1))) :=
          Summable.tsum_le_tsum hbound hdef ((habs.mul_left _).add (hsS.mul_left _))
      _ = ε' * F.card * A + F.card * ∑' p, |φ p| * (if p ∈ S then 0 else 1) := by
          rw [Summable.tsum_add (habs.mul_left _) (hsS.mul_left _), tsum_mul_left, tsum_mul_left]
      _ ≤ ε' * F.card * A + F.card * (ε / 4) := by
          gcongr
  have hdiff : F.card * ∑' p, ψ p - ∑' p, ψ p * c p = ∑' p, ψ p * (F.card - c p) := by
    rw [← tsum_mul_left, ← Summable.tsum_sub (hψ.mul_left _) hψc]
    exact tsum_congr fun p => by ring
  have hdiffle : |∑' p, ψ p * (F.card - c p)| ≤ ∑' p, |φ p| * (F.card - c p) := by
    have hs3 : Summable fun p => ψ p * (F.card - c p) :=
      Summable.of_norm_bounded hdef fun p => by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hc_le p] : (0 : ℝ) ≤ F.card - c p)]
        exact mul_le_mul_of_nonneg_right (hψφ p) (by linarith [hc_le p])
    rw [← Real.norm_eq_abs]
    refine (norm_tsum_le_tsum_norm hs3.norm).trans (Summable.tsum_le_tsum (fun p => ?_) hs3.norm hdef)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by linarith [hc_le p] : (0 : ℝ) ≤ F.card - c p)]
    exact mul_le_mul_of_nonneg_right (hψφ p) (by linarith [hc_le p])
  -- Conclude `Σ ψ ≥ −(ε' A + ε/4) > −ε`.
  have hmain : F.card * ∑' p, ψ p ≥ -(ε' * F.card * A + F.card * (ε / 4)) := by
    have := (abs_le.mp (hdiffle.trans hdefle)).1
    linarith
  have hε'A : ε' * A ≤ ε / 4 := by
    have hA1 : A + 1 ≠ 0 := by linarith
    calc ε' * A = ε * A / (4 * (A + 1)) := by simp only [ε']; ring
      _ ≤ ε * (A + 1) / (4 * (A + 1)) := by gcongr; linarith
      _ = ε / 4 := by field_simp
  have : -(ε' * A + ε / 4) ≤ ∑' p, ψ p := by
    have h := hmain
    rw [ge_iff_le, show -(ε' * F.card * A + F.card * (ε / 4)) =
      F.card * (-(ε' * A + ε / 4)) by ring] at h
    exact le_of_mul_le_mul_left h hF0
  linarith

/-- **Bochner positivity in `ℓ¹`.** -/
theorem IsEvenPosDef.tsum_mul_cos_nonneg {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (hs : Summable φ)
    (θ : Γ →+ ℝ) : 0 ≤ ∑' γ, φ γ * Real.cos (θ γ) :=
  tsum_nonneg_of_gram hs (fun γ => by
    rw [abs_mul]; exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _))
    (hφ.sum_sum_cos_nonneg θ)

end Positivity

/-! ### Realization -/

section Realization

variable {Γ : Type*} [AddCommGroup Γ]

/-- The Bohr series `B(s) = Σ_γ φ(γ) cos(s h(γ))`. -/
noncomputable def bohrSeries (φ : Γ → ℝ) (h : Γ →+ ℝ) (s : ℝ) : ℝ :=
  ∑' γ, φ γ * Real.cos (s * h γ)

/-- The pushforward `D_h(u) = Σ_{h(γ) = u} φ(γ)`. -/
noncomputable def pushDivisor (φ : Γ → ℝ) (h : Γ →+ ℝ) (u : ℝ) : ℝ :=
  ∑' γ, φ γ * diracAt (u - h γ)

/-- Von Mangoldt weights twisted by the Bohr series. -/
noncomputable def bohrWeight (φ : Γ → ℝ) (h : Γ →+ ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  zetaBoundaryWeight x n * bohrSeries φ h (logFrequency n)

theorem bohrSeries_nonneg {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (hs : Summable φ) (h : Γ →+ ℝ)
    (s : ℝ) : 0 ≤ bohrSeries φ h s := by
  have := hφ.tsum_mul_cos_nonneg hs (s • h)
  simp only [AddMonoidHom.smul_apply, smul_eq_mul] at this
  exact this

theorem abs_bohrSeries_le {φ : Γ → ℝ} (hs : Summable φ) (h : Γ →+ ℝ) (s : ℝ) :
    |bohrSeries φ h s| ≤ ∑' γ, |φ γ| := by
  have hb : Summable fun γ => φ γ * Real.cos (s * h γ) :=
    Summable.of_norm_bounded hs.abs fun γ => by
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
  rw [← Real.norm_eq_abs]
  refine (norm_tsum_le_tsum_norm hb.norm).trans (Summable.tsum_le_tsum (fun γ => ?_) hb.norm hs.abs)
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)

/-- The twisted trace is the `φ`-average of shifted ζ-traces. -/
theorem trace_bohrWeight {φ : Γ → ℝ} (hs : Summable φ) (h : Γ →+ ℝ) {x : ℝ} (hx : 0 < x)
    (u : ℝ) :
    cosineTrace (bohrWeight φ h x) logFrequency u = ∑' γ, φ γ *
      ((cosineTrace (zetaBoundaryWeight x) logFrequency (u - h γ) +
        cosineTrace (zetaBoundaryWeight x) logFrequency (u + h γ)) / 2) := by
  have hz := summable_zetaBoundaryWeight hx
  have hz0 := zetaBoundaryWeight_nonneg x
  set f : ℕ → Γ → ℝ := fun n γ => zetaBoundaryWeight x n * (φ γ * Real.cos (logFrequency n * h γ)) *
    Real.cos (logFrequency n * u)
  have hf : Summable (Function.uncurry f) := by
    refine Summable.of_norm_bounded (Summable.mul_of_nonneg hz hs.abs hz0 fun γ => abs_nonneg _)
      fun p => ?_
    obtain ⟨n, γ⟩ := p
    simp only [Function.uncurry_apply_pair, f, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (hz0 n)]
    have h1 := Real.abs_cos_le_one (logFrequency n * h γ)
    have h2 := Real.abs_cos_le_one (logFrequency n * u)
    have h3 := abs_nonneg (φ γ)
    calc zetaBoundaryWeight x n * (|φ γ| * |Real.cos (logFrequency n * h γ)|) *
          |Real.cos (logFrequency n * u)| ≤ zetaBoundaryWeight x n * (|φ γ| * 1) * 1 :=
          mul_le_mul (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 h3) (hz0 n)) h2
            (abs_nonneg _) (mul_nonneg (hz0 n) (by linarith))
      _ = _ := by ring
  have hrow : ∀ n, HasSum (f n) (zetaBoundaryWeight x n * bohrSeries φ h (logFrequency n) *
      Real.cos (logFrequency n * u)) := fun n => by
    have hb : Summable fun γ => φ γ * Real.cos (logFrequency n * h γ) :=
      Summable.of_norm_bounded hs.abs fun γ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (Real.abs_cos_le_one _)
    exact (hb.hasSum.mul_left (zetaBoundaryWeight x n)).mul_right _
  have hcol : ∀ γ, ∑' n, f n γ = φ γ *
      ((cosineTrace (zetaBoundaryWeight x) logFrequency (u - h γ) +
        cosineTrace (zetaBoundaryWeight x) logFrequency (u + h γ)) / 2) := fun γ => by
    have hA := summable_cosineTrace_terms hz0 hz logFrequency (u - h γ)
    have hB := summable_cosineTrace_terms hz0 hz logFrequency (u + h γ)
    unfold cosineTrace
    rw [← Summable.tsum_add hA hB, ← tsum_div_const, ← tsum_mul_left]
    refine tsum_congr fun n => ?_
    simp only [f]
    rw [show logFrequency n * (u - h γ) = logFrequency n * u - logFrequency n * h γ by ring,
      show logFrequency n * (u + h γ) = logFrequency n * u + logFrequency n * h γ by ring,
      Real.cos_sub, Real.cos_add]
    ring
  unfold cosineTrace bohrWeight
  calc ∑' n, zetaBoundaryWeight x n * bohrSeries φ h (logFrequency n) *
        Real.cos (logFrequency n * u) = ∑' n, ∑' γ, f n γ :=
        tsum_congr fun n => (hrow n).tsum_eq.symm
    _ = ∑' γ, ∑' n, f n γ := hf.tsum_comm.symm
    _ = _ := tsum_congr hcol

/-- **Realization of summable positive-definite configurations.** -/
theorem summable_isBoundaryDivisor {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (hs : Summable φ)
    (h : Γ →+ ℝ) : IsBoundaryDivisor logFrequency (bohrWeight φ h) (pushDivisor φ h) where
  nonneg x _ n := mul_nonneg (zetaBoundaryWeight_nonneg x n) (bohrSeries_nonneg hφ hs h _)
  summable x hx := Summable.of_nonneg_of_le
    (fun n => mul_nonneg (zetaBoundaryWeight_nonneg x n) (bohrSeries_nonneg hφ hs h _))
    (fun n => mul_le_mul_of_nonneg_left ((le_abs_self _).trans (abs_bohrSeries_le hs h _))
      (zetaBoundaryWeight_nonneg x n))
    ((summable_zetaBoundaryWeight hx).mul_right _)
  tendsto u := by
    have hz : ∀ v, Tendsto (fun x => x * cosineTrace (zetaBoundaryWeight x) logFrequency v)
        (𝓝[>] 0) (𝓝 (diracAt v)) := fun v => by
      have := zeta_isBoundaryDivisor.tendsto v
      rwa [zetaBoundaryDivisor_eq] at this
    -- Near `0`, `x · tr(x, w) ≤ x · tr(x, 0) ≤ 2`.
    have hev : ∀ᶠ x in 𝓝[>] 0, 0 < x ∧ x * cosineTrace (zetaBoundaryWeight x) logFrequency 0 ≤ 2 :=
      (eventually_mem_nhdsWithin.mono fun x (hx : x ∈ Set.Ioi (0 : ℝ)) => (hx : 0 < x)).and
        ((hz 0).eventually (ge_mem_nhds (by simp [diracAt])))
    have hbd : ∀ x, 0 < x → x * cosineTrace (zetaBoundaryWeight x) logFrequency 0 ≤ 2 →
        ∀ v, |x * cosineTrace (zetaBoundaryWeight x) logFrequency v| ≤ 2 := by
      intro x hx h2 v
      have hz0 := zetaBoundaryWeight_nonneg x
      have hzs := summable_zetaBoundaryWeight hx
      have hle : |cosineTrace (zetaBoundaryWeight x) logFrequency v| ≤
          cosineTrace (zetaBoundaryWeight x) logFrequency 0 := by
        unfold cosineTrace
        simp only [mul_zero, Real.cos_zero, mul_one]
        have ht := summable_cosineTrace_terms hz0 hzs logFrequency v
        rw [← Real.norm_eq_abs]
        refine (norm_tsum_le_tsum_norm ht.norm).trans (Summable.tsum_le_tsum (fun n => ?_)
          ht.norm hzs)
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hz0 n)]
        exact mul_le_of_le_one_right (hz0 n) (Real.abs_cos_le_one _)
      rw [abs_mul, abs_of_pos hx]
      exact (mul_le_mul_of_nonneg_left hle hx.le).trans h2
    have hT := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
      (f := fun x γ => φ γ * ((x * cosineTrace (zetaBoundaryWeight x) logFrequency (u - h γ) +
        x * cosineTrace (zetaBoundaryWeight x) logFrequency (u + h γ)) / 2))
      (g := fun γ => φ γ * ((diracAt (u - h γ) + diracAt (u + h γ)) / 2))
      (bound := fun γ => 2 * |φ γ|) (hs.abs.mul_left 2)
      (fun γ => (((hz _).add (hz _)).div_const 2).const_mul (φ γ))
      (hev.mono fun x hx γ => by
        rw [Real.norm_eq_abs, abs_mul]
        have h1 := hbd x hx.1 hx.2 (u - h γ)
        have h2 := hbd x hx.1 hx.2 (u + h γ)
        have : |(x * cosineTrace (zetaBoundaryWeight x) logFrequency (u - h γ) +
            x * cosineTrace (zetaBoundaryWeight x) logFrequency (u + h γ)) / 2| ≤ 2 := by
          rw [abs_div, abs_two]
          linarith [abs_add_le (x * cosineTrace (zetaBoundaryWeight x) logFrequency (u - h γ))
            (x * cosineTrace (zetaBoundaryWeight x) logFrequency (u + h γ))]
        calc |φ γ| * |(x * cosineTrace (zetaBoundaryWeight x) logFrequency (u - h γ) +
              x * cosineTrace (zetaBoundaryWeight x) logFrequency (u + h γ)) / 2|
            ≤ |φ γ| * 2 := mul_le_mul_of_nonneg_left this (abs_nonneg _)
          _ = 2 * |φ γ| := by ring)
    -- The limit is the pushforward: reflect the `u + h γ` half.
    have hg1 : Summable fun γ => φ γ * diracAt (u - h γ) :=
      Summable.of_norm_bounded hs.abs fun γ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (by unfold diracAt; split_ifs <;> simp)
    have hg2 : Summable fun γ => φ γ * diracAt (u + h γ) :=
      Summable.of_norm_bounded hs.abs fun γ => by
        rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg _) (by unfold diracAt; split_ifs <;> simp)
    have href : ∑' γ, φ γ * diracAt (u + h γ) = ∑' γ, φ γ * diracAt (u - h γ) := by
      rw [← (Equiv.neg Γ).tsum_eq]
      exact tsum_congr fun γ => by simp [hφ.even, sub_eq_add_neg]
    have hlimval : ∑' γ, φ γ * ((diracAt (u - h γ) + diracAt (u + h γ)) / 2) =
        pushDivisor φ h u := by
      rw [show (fun γ => φ γ * ((diracAt (u - h γ) + diracAt (u + h γ)) / 2)) =
        fun γ => (φ γ * diracAt (u - h γ) + φ γ * diracAt (u + h γ)) / 2 from
          funext fun γ => by ring, tsum_div_const, Summable.tsum_add hg1 hg2, href]
      unfold pushDivisor
      ring
    rw [hlimval] at hT
    refine hT.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    rw [trace_bohrWeight hs h hx u, ← tsum_mul_left]
    exact tsum_congr fun γ => by ring

/-- **Integral realization of summable positive-definite configurations.** -/
theorem summable_integral {φ : Γ → ℝ} (hφ : IsEvenPosDef φ) (hs : Summable φ) (h : Γ →+ ℝ) :
    ∃ m : ℕ → ℕ, IsBoundaryDivisor logFrequency (intWeight m) (pushDivisor φ h) :=
  ⟨_, IsBoundaryDivisor.round (g := fun n => bohrSeries φ h (logFrequency n))
    (fun _ => bohrSeries_nonneg hφ hs h _)
    (fun _ => (le_abs_self _).trans (abs_bohrSeries_le hs h _))
    (summable_isBoundaryDivisor hφ hs h)⟩

/-- **Every absolutely summable even positive-definite function on `ℝ` is the boundary divisor of
an integral Euler product**, whatever its support. -/
theorem summable_real_integral {D : ℝ → ℝ} (hD : IsEvenPosDef D) (hs : Summable D) :
    ∃ m : ℕ → ℕ, IsBoundaryDivisor logFrequency (intWeight m) D := by
  obtain ⟨m, hm⟩ := summable_integral hD hs (AddMonoidHom.id ℝ)
  refine ⟨m, ?_⟩
  convert hm using 1
  funext u
  unfold pushDivisor
  rw [tsum_eq_single u fun v hv => by
    simp [diracAt, sub_eq_zero, Ne.symm hv]]
  simp [diracAt]

end Realization

/-! ### Rank-`r` boundary profiles -/

section Rank

variable {r : ℕ}

/-- The heights `k ↦ ⟨k, t⟩ = Σ_i k_i t_i` on `ℤ^r`. -/
def heightHom (t : Fin r → ℝ) : (Fin r → ℤ) →+ ℝ where
  toFun k := ∑ i, (k i : ℝ) * t i
  map_zero' := by simp
  map_add' a b := by simp [add_mul, Finset.sum_add_distrib]

theorem pushDivisor_height {t : Fin r → ℝ} (ht : Function.Injective (heightHom t))
    (d : (Fin r → ℤ) → ℝ) (k : Fin r → ℤ) : pushDivisor d (heightHom t) (heightHom t k) = d k := by
  unfold pushDivisor
  rw [tsum_eq_single k fun k' hk' => by
    rw [diracAt, if_neg (fun h => hk' (ht (sub_eq_zero.mp h)).symm), mul_zero]]
  simp [diracAt]

theorem pushDivisor_off {t : Fin r → ℝ} (d : (Fin r → ℤ) → ℝ) {u : ℝ}
    (hu : u ∉ Set.range (heightHom t)) : pushDivisor d (heightHom t) u = 0 := by
  unfold pushDivisor
  refine (tsum_congr fun k => ?_).trans tsum_zero
  rw [diracAt, if_neg (fun h => hu ⟨k, (sub_eq_zero.mp h).symm⟩), mul_zero]

/-- **Summable rank-`r` profiles are integral boundary profiles.** -/
theorem rank_profile_integral {t : Fin r → ℝ} {d : (Fin r → ℤ) → ℝ} (hd : IsEvenPosDef d)
    (hs : Summable d) :
    ∃ m : ℕ → ℕ, IsBoundaryDivisor logFrequency (intWeight m) (pushDivisor d (heightHom t)) :=
  summable_integral hd hs (heightHom t)

/-- **Rank collapse.** An integer-valued rank-`r` profile with a unit pole that is a boundary
profile has a support of rank at most one: any two of its points are proportional. -/
theorem rank_profile_collapse {t : Fin r → ℝ} (ht : Function.Injective (heightHom t))
    {d : (Fin r → ℤ) → ℝ} {ι : Type*} {lam : ι → ℝ} {w : ℝ → ι → ℝ}
    (hw : IsBoundaryDivisor lam w (pushDivisor d (heightHom t))) (h0 : d 0 = 1)
    (hint : ∀ k, ∃ n : ℤ, d k = n) {k k' : Fin r → ℤ} (hk : d k ≠ 0) (hk' : d k' ≠ 0) :
    ∃ m m' : ℤ, (m ≠ 0 ∨ m' ≠ 0) ∧ m • k = m' • k' := by
  have hD0 : pushDivisor d (heightHom t) 0 = 1 := by
    rw [show (0 : ℝ) = heightHom t 0 from (map_zero _).symm, pushDivisor_height ht, h0]
  have hDint : ∀ u, ∃ n : ℤ, pushDivisor d (heightHom t) u = n := fun u => by
    by_cases hu : u ∈ Set.range (heightHom t)
    · obtain ⟨j, rfl⟩ := hu
      rw [pushDivisor_height ht]
      exact hint j
    · exact ⟨0, by rw [pushDivisor_off d hu]; simp⟩
  rcases nonvanishing_cyclic_or_univ hw hD0 hDint with ⟨a, ha⟩ | hall
  · obtain ⟨j, hj⟩ := ha _ (by rw [pushDivisor_height ht]; exact hk)
    obtain ⟨j', hj'⟩ := ha _ (by rw [pushDivisor_height ht]; exact hk')
    have hzero : heightHom t (j' • k - j • k') = 0 := by
      rw [map_sub, map_zsmul, map_zsmul, hj, hj', zsmul_eq_mul, zsmul_eq_mul]
      ring
    have heq : j' • k = j • k' := sub_eq_zero.mp (ht (hzero.trans (map_zero _).symm))
    by_cases hj0 : j' = 0 ∧ j = 0
    · obtain ⟨rfl, rfl⟩ := hj0
      have hk0 : k = 0 := ht (by rw [hj, map_zero]; simp)
      exact ⟨1, 0, Or.inl one_ne_zero, by simp [hk0]⟩
    · exact ⟨j', j, by tauto, heq⟩
  · exfalso
    have hrange : Set.range (heightHom t) = Set.univ :=
      Set.eq_univ_of_forall fun u => by
        by_contra hu
        exact hall u (pushDivisor_off d hu)
    exact Cardinal.not_countable_real (hrange ▸ Set.countable_range _)

end Rank

end GaloisForLFunctions.MultiplicativePositivityGeometry
