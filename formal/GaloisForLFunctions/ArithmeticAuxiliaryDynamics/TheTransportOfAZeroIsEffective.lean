import GaloisForLFunctions.ArithmeticAuxiliaryDynamics.TheMissingInputOfTransport
import GaloisForLFunctions.HTGeometry.ThreeCircles
import GaloisForLFunctions.HTGeometry.DirichletSimultaneousApproximation
import GaloisForLFunctions.VerifiedHeightRungs.HadamardBudget.TheVerifiedHeightSixtySeven
import GaloisForLFunctions.VerifiedHeightRungs.LiAndHausdorffEntries

/-!
# The transport of a zero is effective

Boundedness of the translates is more than transport needs. Suppose the phases of `1, …, N` are within `1/N` of `1` at the shift `τ`.
On `Re s ≥ 2` the translate differs from `ζ` by at most `4/N`. On a disc about `3 + iγ` reaching past a zero `ρ = β + iγ`, let `|ζ(s + iτ)| ≤ M`.
Then Hadamard's three circles interpolate:

`|ζ(s + iτ) − ζ(s)| ≤ (4/N)^{1−t} (2M)^t`,

with `t < 1` depending only on `ρ` and the circle. Rouché moves the zero as soon as this is small.

**So a polynomial bound in the aligned length suffices.** For each zero there is an exponent `A > 0` such that, at every shift aligned up
to `N ≥ N₀`, a bound `|ζ(s + iτ)| ≤ N^A` on the disc puts a zero within `r` of `ρ + iτ`. By simultaneous Dirichlet approximation a shift aligned up to
`N` exists with `1 ≤ τ ≤ (7N)^N`. At such a shift `N ≥ log τ / log (7N)`, so the bound allowed is at least a power of `log τ`, up to a factor
that is a power of `log N`.

The contrapositive is a lower bound. If only finitely many zeros lie right of `σ`, then at every aligned shift, past a height, `ζ` is larger
than `N^A` somewhere on the disc about each zero right of `σ`. This is the local form of the missing input of transport: the question is whether an aligned shift
exists at which `ζ` is only polylogarithmically large across a disc that crosses the line `Re s = 1`.
-/

open Complex Filter Topology Metric Set
open GaloisForLFunctions.ArithmeticKreinLangerTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticAuxiliaryDynamics

/-- The phases of `1, …, N` are within `1/N` of `1` at the shift `τ`. -/
def IsHeadReturn (N : ℕ) (τ : ℝ) : Prop :=
  ∀ n < N, ‖phaseDefect (fun _ => τ) 0 n‖ ≤ 1 / (N : ℝ)

/-- **Aligned shifts exist at bounded height.** By simultaneous Dirichlet approximation, a shift aligned up to `N` exists with `1 ≤ τ ≤ (7N)^N`. -/
theorem exists_isHeadReturn_le {N : ℕ} (hN : 1 ≤ N) :
    ∃ τ : ℝ, 1 ≤ τ ∧ τ ≤ ((7 * N : ℕ) : ℝ) ^ N ∧ IsHeadReturn N τ := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  obtain ⟨k, hk1, hkQ, hclose⟩ := HTGeometry.exists_dirichlet_simultaneous
    (fun i : Fin N => Real.log (((i : ℕ) : ℝ) + 1) / (2 * Real.pi)) (7 * N) (by omega)
  rw [Fintype.card_fin] at hkQ
  refine ⟨k, by exact_mod_cast hk1, by exact_mod_cast hkQ, fun n hn => ?_⟩
  obtain ⟨m, hm⟩ := hclose ⟨n, hn⟩
  simp only at hm
  obtain ⟨e, he⟩ : ∃ e : ℝ, e = (k : ℝ) * (Real.log ((n : ℝ) + 1) / (2 * Real.pi)) - m := ⟨_, rfl⟩
  rw [← he] at hm
  have hkey : -Real.log ((n : ℝ) + 1) * (k : ℝ) = -(2 * Real.pi * e) + (-m : ℤ) * (2 * Real.pi) := by
    rw [he]
    push_cast
    field_simp
    ring
  rw [phaseDefect_eq]
  simp only
  rw [hkey]
  have hexp : exp (((-(2 * Real.pi * e) + (-m : ℤ) * (2 * Real.pi) : ℝ) : ℂ) * I) =
      exp (((-(2 * Real.pi * e) : ℝ) : ℂ) * I) := by
    push_cast
    rw [add_mul, Complex.exp_add]
    have h1 : ((-(m : ℂ)) * (2 * (Real.pi : ℂ))) * I = ((-m : ℤ) : ℂ) * (2 * (Real.pi : ℂ) * I) := by
      push_cast
      ring
    rw [h1, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  rw [hexp, mul_comm _ I]
  refine (Complex.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
  have hpi2 := Real.pi_lt_d2
  have hQ : (0 : ℝ) < ((7 * N : ℕ) : ℝ) := by positivity
  have h2 : 2 * Real.pi * |e| ≤ 2 * Real.pi * (1 / ((7 * N : ℕ) : ℝ)) :=
    mul_le_mul_of_nonneg_left hm.le (by positivity)
  refine h2.trans ?_
  push_cast
  rw [mul_one_div, div_le_div_iff₀ (by positivity) hNR]
  nlinarith

private lemma norm_zetaTerm_le {w : ℂ} (hw : 2 ≤ w.re) (n : ℕ) :
    ‖zetaTerm w n‖ ≤ 1 / ((n : ℝ) + 1) ^ 2 := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  rw [norm_zetaTerm]
  calc ((n : ℝ) + 1) ^ (-w.re) ≤ ((n : ℝ) + 1) ^ (-2 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le h1 (by linarith)
    _ = _ := by
        rw [Real.rpow_neg (by linarith), Real.rpow_two, one_div]

private lemma sum_Ico_inv_sq_le {N m : ℕ} (hN : 1 ≤ N) (hNm : N ≤ m) :
    ∑ n ∈ Finset.Ico N m, 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 / (N : ℝ) - 1 / (m : ℝ) := by
  induction m, hNm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [Finset.sum_Ico_succ_top hm]
    have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hstep : 1 / ((m : ℝ) + 1) ^ 2 ≤ 1 / (m : ℝ) - 1 / ((m + 1 : ℕ) : ℝ) := by
      push_cast
      rw [div_sub_div _ _ hm0.ne' (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith
    linarith

/-- **An aligned shift returns to the right of the strip.** -/
theorem norm_sub_le_of_isHeadReturn {N : ℕ} {τ : ℝ} (hN : 1 ≤ N) (h : IsHeadReturn N τ) {s : ℂ} (hs : 2 ≤ s.re) :
    ‖riemannZeta (s + (τ : ℂ) * I) - riemannZeta s‖ ≤ 4 / (N : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hsum := hasSum_translateDiff (fun _ => τ) 0 (by linarith : 1 < s.re)
  have hpart : ∀ m, ‖∑ n ∈ Finset.range m, zetaTerm s n * phaseDefect (fun _ => τ) 0 n‖ ≤ 4 / (N : ℝ) := by
    intro m
    refine (norm_sum_le _ _).trans ?_
    have hterm : ∀ n, ‖zetaTerm s n * phaseDefect (fun _ => τ) 0 n‖ ≤
        1 / ((n : ℝ) + 1) ^ 2 * (if n < N then 1 / (N : ℝ) else 2) := by
      intro n
      rw [norm_mul]
      refine mul_le_mul (norm_zetaTerm_le hs n) ?_ (norm_nonneg _) (by positivity)
      split_ifs with hn
      · exact h n hn
      · exact norm_phaseDefect_le _ _ _
    refine (Finset.sum_le_sum fun n _ => hterm n).trans ?_
    -- Below `N` the phases are aligned; above `N` the tail is small.
    obtain ⟨M, hM⟩ : ∃ M, M = max m N := ⟨_, rfl⟩
    have hmM : m ≤ M := hM ▸ le_max_left _ _
    have hNM : N ≤ M := hM ▸ le_max_right _ _
    have hnn : ∀ n : ℕ, 0 ≤ 1 / ((n : ℝ) + 1) ^ 2 * (if n < N then 1 / (N : ℝ) else 2) := fun n => by
      split_ifs <;> positivity
    refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr hmM)
      fun n _ _ => hnn n).trans ?_
    rw [Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le N) hNM]
    have hlow : ∑ n ∈ Finset.Ico 0 N, 1 / ((n : ℝ) + 1) ^ 2 * (if n < N then 1 / (N : ℝ) else 2) ≤
        2 / (N : ℝ) := by
      have h1 : ∑ n ∈ Finset.Ico 0 N, 1 / ((n : ℝ) + 1) ^ 2 * (if n < N then 1 / (N : ℝ) else 2) =
          (∑ n ∈ Finset.Ico 0 N, 1 / ((n : ℝ) + 1) ^ 2) * (1 / (N : ℝ)) := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [if_pos (Finset.mem_Ico.mp hn).2]
      have h2 : ∑ n ∈ Finset.Ico 0 N, 1 / ((n : ℝ) + 1) ^ 2 ≤ 2 := by
        rw [← Finset.sum_Ico_consecutive _ (Nat.zero_le 1) hN]
        have h3 : ∑ n ∈ Finset.Ico 1 N, 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 - 1 / (N : ℝ) := by
          have h5 := sum_Ico_inv_sq_le (N := 1) (m := N) le_rfl hN
          rwa [Nat.cast_one, div_one] at h5
        have h4 : (0 : ℝ) ≤ 1 / (N : ℝ) := by positivity
        have hone : ∑ n ∈ Finset.Ico 0 1, 1 / (((n : ℕ) : ℝ) + 1) ^ 2 = 1 := by simp
        rw [hone]
        linarith
      rw [h1]
      calc _ ≤ 2 * (1 / (N : ℝ)) := mul_le_mul_of_nonneg_right h2 (by positivity)
        _ = _ := by ring
    have hhigh : ∑ n ∈ Finset.Ico N M, 1 / ((n : ℝ) + 1) ^ 2 * (if n < N then 1 / (N : ℝ) else 2) ≤
        2 / (N : ℝ) := by
      have h1 : ∑ n ∈ Finset.Ico N M, 1 / ((n : ℝ) + 1) ^ 2 * (if n < N then 1 / (N : ℝ) else 2) =
          (∑ n ∈ Finset.Ico N M, 1 / ((n : ℝ) + 1) ^ 2) * 2 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun n hn => ?_
        rw [if_neg (not_lt.mpr (Finset.mem_Ico.mp hn).1)]
      have h2 := sum_Ico_inv_sq_le hN hNM
      have hMpos : (0 : ℝ) ≤ 1 / (M : ℝ) := by positivity
      rw [h1]
      calc _ ≤ (1 / (N : ℝ)) * 2 := mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
        _ = _ := by ring
    calc _ ≤ 2 / (N : ℝ) + 2 / (N : ℝ) := add_le_add hlow hhigh
      _ = _ := by ring
  have hlim := hsum.tendsto_sum_nat.norm
  have hval : translateDiff (fun _ => τ) 0 s = riemannZeta (s + (τ : ℂ) * I) - riemannZeta s := rfl
  rw [hval] at hlim
  exact le_of_tendsto hlim (Eventually.of_forall hpart)

/-- The geometric interpolation is monotone in its exponent. -/
private lemma interp_mono {a b s t : ℝ} (ha : 0 < a) (hab : a ≤ b) (hst : s ≤ t) :
    a ^ (1 - s) * b ^ s ≤ a ^ (1 - t) * b ^ t := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have hform : ∀ x : ℝ, a ^ (1 - x) * b ^ x = a * (b / a) ^ x := by
    intro x
    rw [Real.div_rpow hb.le ha.le, Real.rpow_sub ha, Real.rpow_one]
    field_simp
  rw [hform, hform]
  refine mul_le_mul_of_nonneg_left ?_ ha.le
  exact Real.rpow_le_rpow_of_exponent_le ((one_le_div ha).mpr hab) hst

/-- The arithmetic of the interpolated bound. -/
private lemma interp_value {N A t : ℝ} (hN : 1 ≤ N) (ht0 : 0 < t) (ht1 : t < 1)
    (hAt : A * t = (1 - t) / 2) :
    (4 / N) ^ (1 - t) * (2 * N ^ A) ^ t ≤ 8 * N ^ (-((1 - t) / 2)) := by
  have hN0 : 0 < N := by linarith
  have hNA : 0 < N ^ A := Real.rpow_pos_of_pos hN0 _
  have h1 : (4 / N) ^ (1 - t) ≤ 4 * N ^ (-(1 - t)) := by
    rw [Real.div_rpow (by norm_num) hN0.le, Real.rpow_neg hN0.le, div_eq_mul_inv]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (4 : ℝ) ^ (1 - t) ≤ (4 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = 4 := Real.rpow_one 4
  have h2 : (2 * N ^ A) ^ t ≤ 2 * N ^ ((1 - t) / 2) := by
    rw [Real.mul_rpow (by norm_num) hNA.le, ← Real.rpow_mul hN0.le, hAt]
    refine mul_le_mul_of_nonneg_right ?_ (by positivity)
    calc (2 : ℝ) ^ t ≤ (2 : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) ht1.le
      _ = 2 := Real.rpow_one 2
  calc (4 / N) ^ (1 - t) * (2 * N ^ A) ^ t
      ≤ (4 * N ^ (-(1 - t))) * (2 * N ^ ((1 - t) / 2)) :=
        mul_le_mul h1 h2 (by positivity) (by positivity)
    _ = 8 * (N ^ (-(1 - t)) * N ^ ((1 - t) / 2)) := by ring
    _ = _ := by
        rw [← Real.rpow_add hN0]
        congr 2
        ring

/-- The disc about `3 + iγ` of radius `31/10`, for `γ ≥ 3`, avoids the pole, and so does each translate by `τ ≥ 1`. -/
private lemma transport_disc_ne_one {γ : ℝ} (hγ : 3 ≤ γ) {w : ℂ} (hw : ‖w‖ ≤ 31 / 10) :
    w + ((3 : ℂ) + (γ : ℂ) * I) ≠ 1 := by
  intro h
  have hw' : w = 1 - ((3 : ℂ) + (γ : ℂ) * I) := by rw [← h]; ring
  have hsq : ‖w‖ ^ 2 = 4 + γ ^ 2 := by
    rw [hw', ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp
    ring
  have hle : ‖w‖ ^ 2 ≤ (31 / 10 : ℝ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hw 2
  nlinarith

private lemma transport_disc_translate_ne_one {γ τ : ℝ} (hγ : 3 ≤ γ) (hτ : 1 ≤ τ) {w : ℂ}
    (hw : ‖w‖ ≤ 31 / 10) : w + ((3 : ℂ) + (γ : ℂ) * I) + (τ : ℂ) * I ≠ 1 := by
  intro h
  have him := congrArg Complex.im h
  have hbd := Complex.abs_im_le_norm w
  have hlow := (abs_le.mp (hbd.trans hw)).1
  simp at him
  linarith

/-- **The local transport theorem.** For a zero `ρ = β + iγ` with `0 < β < 1`, `γ ≥ 3`, and each `r > 0`, there is an exponent `A > 0` such that
at every shift aligned up to a large `N`, a bound `|ζ(s + iτ)| ≤ N^A` on the disc about `3 + iγ` of radius `31/10` puts a zero within `r`
of `ρ + iτ`. -/
theorem exists_exponent_transport {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 3 ≤ ρ.im)
    {r : ℝ} (hr : 0 < r) :
    ∃ A : ℝ, 0 < A ∧ ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ τ : ℝ, 1 ≤ τ → IsHeadReturn N τ →
      (∀ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) (31 / 10), ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ A) →
      ∃ z ∈ ball ρ r, riemannZeta (z + (τ : ℂ) * I) = 0 := by
  have hρne : ρ ≠ 1 := fun h => by
    rw [h, one_re] at h1
    exact lt_irrefl _ h1
  obtain ⟨r₂, hr₂def⟩ : ∃ r₂, r₂ = min r (min (1 / 20) ((1 - ρ.re) / 2)) := ⟨_, rfl⟩
  have hr₂ : 0 < r₂ := by
    rw [hr₂def]
    exact lt_min hr (lt_min (by norm_num) (by linarith))
  obtain ⟨r', m, hr'0, hr'lt, hsub, hm0, hmS⟩ :=
    exists_isolating_circle hρne hρ (ball_mem_nhds ρ hr₂) hr₂
  have hr'1 : r' < 1 / 20 := hr'lt.trans_le (hr₂def ▸ (min_le_right _ _).trans (min_le_left _ _))
  have hr'2 : r' < (1 - ρ.re) / 2 := hr'lt.trans_le (hr₂def ▸ (min_le_right _ _).trans (min_le_right _ _))
  have hr'r : r' < r := hr'lt.trans_le (hr₂def ▸ min_le_left _ _)
  obtain ⟨c, hc⟩ : ∃ c : ℂ, c = (3 : ℂ) + (ρ.im : ℂ) * I := ⟨_, rfl⟩
  have hcρ : ‖ρ - c‖ = 3 - ρ.re := by
    have hval : ρ - c = ((ρ.re - 3 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp [hc]
    rw [hval, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
    ring
  obtain ⟨D, hD⟩ : ∃ D, D = 3 - ρ.re + r' := ⟨_, rfl⟩
  have hD1 : 1 < D := by rw [hD]; linarith
  have hDR : D < 31 / 10 := by rw [hD]; linarith
  have hlogR : 0 < Real.log (31 / 10) := Real.log_pos (by norm_num)
  obtain ⟨t, ht⟩ : ∃ t, t = Real.log D / Real.log (31 / 10) := ⟨_, rfl⟩
  have ht0 : 0 < t := by
    rw [ht]
    exact div_pos (Real.log_pos hD1) hlogR
  have ht1 : t < 1 := by
    rw [ht, div_lt_one hlogR]
    exact Real.log_lt_log (by linarith) hDR
  obtain ⟨A, hA⟩ : ∃ A, A = (1 - t) / (2 * t) := ⟨_, rfl⟩
  have hA0 : 0 < A := by
    rw [hA]
    exact div_pos (by linarith) (by positivity)
  have hAt : A * t = (1 - t) / 2 := by
    rw [hA]
    field_simp
  -- The size of `ζ` itself on the disc.
  have hcont : ContinuousOn riemannZeta (closedBall c (31 / 10)) := by
    intro s hs
    have hw : ‖s - c‖ ≤ 31 / 10 := by
      rwa [mem_closedBall, dist_eq_norm] at hs
    have hne := transport_disc_ne_one hγ hw
    rw [← hc, sub_add_cancel] at hne
    exact (differentiableAt_riemannZeta hne).continuousAt.continuousWithinAt
  obtain ⟨M₀, hM₀⟩ := (isCompact_closedBall c (31 / 10 : ℝ)).exists_bound_of_continuousOn hcont
  -- A large aligned length.
  have hN1 : Tendsto (fun N : ℕ => (N : ℝ) ^ A) atTop atTop :=
    (tendsto_rpow_atTop hA0).comp tendsto_natCast_atTop_atTop
  have hN2 : Tendsto (fun N : ℕ => 8 * (N : ℝ) ^ (-((1 - t) / 2))) atTop (𝓝 0) := by
    have := ((tendsto_rpow_neg_atTop (by linarith : 0 < (1 - t) / 2)).comp
      tendsto_natCast_atTop_atTop).const_mul 8
    simpa using this
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((hN1.eventually_ge_atTop M₀).and
    ((hN2.eventually (gt_mem_nhds (by positivity : 0 < m / 2))).and (eventually_ge_atTop 2)))
  refine ⟨A, hA0, N₀, fun N hN τ hτ hhead hbd => ?_⟩
  obtain ⟨hNM, hNsmall, hN2'⟩ := hN₀ N hN
  have hNR : (2 : ℝ) ≤ N := by exact_mod_cast hN2'
  have hN0R : (0 : ℝ) < N := by linarith
  have hNA1 : 1 ≤ (N : ℝ) ^ A := Real.one_le_rpow (by linarith) hA0.le
  -- The three circles.
  have hbound : ∀ z ∈ closedBall ρ r', ‖riemannZeta (z + (τ : ℂ) * I) - riemannZeta z‖ < m / 2 := by
    intro z hz
    have hzρ : ‖z - ρ‖ ≤ r' := by
      rwa [mem_closedBall, dist_eq_norm] at hz
    obtain ⟨w, hw⟩ : ∃ w, w = z - c := ⟨_, rfl⟩
    have hwc : w + c = z := by rw [hw]; ring
    have hwle : ‖w‖ ≤ D := by
      have h2 : w = (z - ρ) + (ρ - c) := by rw [hw]; ring
      rw [h2, hD, ← hcρ]
      refine (norm_add_le _ _).trans ?_
      linarith
    have hwge : 1 ≤ ‖w‖ := by
      have h2 : ρ - c = -(z - ρ) + w := by rw [hw]; ring
      have h3 : ‖ρ - c‖ ≤ ‖z - ρ‖ + ‖w‖ := by
        rw [h2]
        refine (norm_add_le _ _).trans ?_
        rw [norm_neg]
      rw [hcρ] at h3
      linarith
    obtain ⟨f, hf⟩ : ∃ f : ℂ → ℂ, f = fun w => riemannZeta (w + c + (τ : ℂ) * I) - riemannZeta (w + c) := ⟨_, rfl⟩
    have hd : ∀ y : ℂ, 1 ≤ ‖y‖ → ‖y‖ ≤ 31 / 10 → DifferentiableAt ℂ f y := by
      intro y _ hy
      have hne1 := transport_disc_ne_one hγ hy
      have hne2 := transport_disc_translate_ne_one hγ hτ hy
      rw [← hc] at hne1 hne2
      rw [hf]
      refine DifferentiableAt.sub ?_ ?_
      · exact (differentiableAt_riemannZeta hne2).comp y
          ((differentiableAt_id.add_const c).add_const _)
      · exact (differentiableAt_riemannZeta hne1).comp y (differentiableAt_id.add_const c)
    have hM1 : ∀ y : ℂ, ‖y‖ = 1 → ‖f y‖ ≤ 4 / (N : ℝ) := by
      intro y hy
      have hre : 2 ≤ (y + c).re := by
        have h3 := (abs_le.mp ((Complex.abs_re_le_norm y).trans hy.le)).1
        simp [hc]
        linarith
      rw [hf]
      exact norm_sub_le_of_isHeadReturn (by omega) hhead hre
    have hM3 : ∀ y : ℂ, ‖y‖ = 31 / 10 → ‖f y‖ ≤ 2 * (N : ℝ) ^ A := by
      intro y hy
      have hmem : y + c ∈ closedBall c (31 / 10) := by
        rw [mem_closedBall, dist_eq_norm, add_sub_cancel_right, hy]
      rw [hf]
      refine (norm_sub_le _ _).trans ?_
      have h3 := hbd (y + c) (hc ▸ hmem)
      have h4 := hM₀ _ hmem
      linarith
    have hthree := HTGeometry.norm_le_of_three_circles (f := f) (r₁ := 1) (r₃ := 31 / 10)
      one_pos (by norm_num) hd hM1 hM3 hwge (by linarith)
    rw [Real.log_one, sub_zero, sub_zero] at hthree
    have hfz : f w = riemannZeta (z + (τ : ℂ) * I) - riemannZeta z := by
      rw [hf]
      simp only [hwc]
    rw [hfz] at hthree
    have hs : Real.log ‖w‖ / Real.log (31 / 10) ≤ t := by
      rw [ht]
      refine div_le_div_of_nonneg_right ?_ hlogR.le
      exact Real.log_le_log (by linarith) hwle
    have h4N : 4 / (N : ℝ) ≤ 2 * (N : ℝ) ^ A := by
      have : 4 / (N : ℝ) ≤ 2 := by
        rw [div_le_iff₀ hN0R]
        linarith
      linarith
    refine lt_of_le_of_lt (hthree.trans ((interp_mono (by positivity) h4N hs).trans ?_)) hNsmall
    exact interp_value (by linarith) ht0 ht1 hAt
  have hre : ∀ s ∈ closedBall ρ r', s.re < 1 := by
    intro s hs
    have h2 : ‖s - ρ‖ ≤ r' := by
      rwa [mem_closedBall, dist_eq_norm] at hs
    have h3 := (abs_le.mp ((Complex.abs_re_le_norm (s - ρ)).trans h2)).2
    rw [Complex.sub_re] at h3
    linarith
  obtain ⟨z, hz, hzero⟩ := RHTower.exists_zero_of_mem_zetaReturnSet hr'0 hre hρ hmS hbound
  exact ⟨z, ball_subset_ball hr'r.le hz, hzero⟩

/-- **The lower bound behind a finite top layer.** If finitely many zeros lie right of `σ`, then for each zero right of `σ` there is an exponent `A > 0` such
that, at every aligned shift past a height, `ζ` exceeds `N^A` somewhere on the disc. -/
theorem exists_large_value_of_finite {σ : ℝ} (hfin : {w : ℂ | riemannZeta w = 0 ∧ σ < w.re}.Finite) {ρ : ℂ}
    (hρ : riemannZeta ρ = 0) (hσ : σ < ρ.re) (h0 : 0 < ρ.re) (h1 : ρ.re < 1) (hγ : 3 ≤ ρ.im) :
    ∃ A : ℝ, 0 < A ∧ ∃ (N₀ : ℕ) (H : ℝ), ∀ N, N₀ ≤ N → ∀ τ : ℝ, H ≤ τ → IsHeadReturn N τ →
      ∃ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) (31 / 10),
        (N : ℝ) ^ A < ‖riemannZeta (s + (τ : ℂ) * I)‖ := by
  obtain ⟨r, hrdef⟩ : ∃ r, r = ρ.re - σ := ⟨_, rfl⟩
  have hr : 0 < r := by rw [hrdef]; linarith
  obtain ⟨A, hA, N₀, hall⟩ := exists_exponent_transport hρ h0 h1 hγ hr
  obtain ⟨Hm, hHm⟩ := (hfin.image Complex.im).bddAbove
  refine ⟨A, hA, N₀, max 1 (Hm - ρ.im + r + 1), fun N hN τ hτ hhead => ?_⟩
  have hτ1 : 1 ≤ τ := (le_max_left _ _).trans hτ
  have hτ2 : Hm - ρ.im + r + 1 ≤ τ := (le_max_right _ _).trans hτ
  by_contra hcon
  push Not at hcon
  obtain ⟨z, hz, hzero⟩ := hall N hN τ hτ1 hhead hcon
  have hzb : ‖z - ρ‖ < r := by
    rwa [mem_ball, dist_eq_norm] at hz
  have hre := (abs_lt.mp ((Complex.abs_re_le_norm (z - ρ)).trans_lt hzb)).1
  have him := (abs_lt.mp ((Complex.abs_im_le_norm (z - ρ)).trans_lt hzb)).1
  rw [Complex.sub_re] at hre
  rw [Complex.sub_im] at him
  have hwre : (z + (τ : ℂ) * I).re = z.re := by simp
  have hwim : (z + (τ : ℂ) * I).im = z.im + τ := by simp
  have hmem : z + (τ : ℂ) * I ∈ {w : ℂ | riemannZeta w = 0 ∧ σ < w.re} :=
    ⟨hzero, by rw [hwre]; linarith⟩
  have hle := hHm ⟨_, hmem, rfl⟩
  rw [hwim] at hle
  linarith

/-- **A slow aligned return at a zero gives infinitely many zeros.** Translates may grow: at each exponent, aligned shifts of arbitrarily large length and height
at which `ζ` stays below `N^A` on the disc force infinitely many zeros right of `ρ.re − r`. -/
theorem infinite_zeros_of_slow_returns {ρ : ℂ} (hρ : riemannZeta ρ = 0) (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hγ : 3 ≤ ρ.im)
    (hslow : ∀ A : ℝ, 0 < A → ∀ (N₀ : ℕ) (H : ℝ), ∃ N, N₀ ≤ N ∧ ∃ τ : ℝ, H ≤ τ ∧ IsHeadReturn N τ ∧
      ∀ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) (31 / 10), ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ A)
    {r : ℝ} (hr : 0 < r) : {w : ℂ | riemannZeta w = 0 ∧ ρ.re - r < w.re}.Infinite := by
  intro hfin
  obtain ⟨A, hA, N₀, H, hall⟩ := exists_large_value_of_finite hfin hρ (by linarith) h0 h1 hγ
  obtain ⟨N, hN, τ, hτ, hhead, hbd⟩ := hslow A hA N₀ H
  obtain ⟨s, hs, hlt⟩ := hall N hN τ hτ hhead
  exact absurd (hbd s hs) (not_le.mpr hlt)

/-- **Slow aligned returns give the asymptotic abscissa law.** It is enough that, at each zero right of `½` in the upper half-plane and each exponent, aligned shifts of arbitrarily large
length and height keep `ζ` below `N^A` on the disc. Zeros right of `½` lie above height `67`, so the disc avoids the pole. -/
theorem asymptoticAbscissaLaw_of_slowReturns
    (hslow : ∀ ρ : ℂ, riemannZeta ρ = 0 → 1 / 2 < ρ.re → ρ.re < 1 → 0 < ρ.im → ∀ A : ℝ, 0 < A →
      ∀ (N₀ : ℕ) (H : ℝ), ∃ N, N₀ ≤ N ∧ ∃ τ : ℝ, H ≤ τ ∧ IsHeadReturn N τ ∧
        ∀ s ∈ closedBall ((3 : ℂ) + (ρ.im : ℂ) * I) (31 / 10),
          ‖riemannZeta (s + (τ : ℂ) * I)‖ ≤ (N : ℝ) ^ A) :
    RHTower.AsymptoticAbscissaLaw := by
  refine asymptoticAbscissaLaw_of_infinite_zeros fun ρ hρ h12 h1 him r hr => ?_
  have hne1 : ρ ≠ 1 := fun h => by
    rw [h, one_re] at h1
    exact lt_irrefl _ h1
  have hxi : RHTower.xi ρ = 0 := (RHTower.xi_eq_zero_iff (by linarith) hne1).mpr hρ
  have hhigh := VerifiedHeightRungs.lt_abs_im_of_rhVerifiedThrough
    VerifiedHeightRungs.HadamardBudget.rhVerifiedThrough_sixtySeven hxi (by linarith) h1 (ne_of_gt h12)
  rw [abs_of_pos him] at hhigh
  exact infinite_zeros_of_slow_returns hρ (by linarith) h1 (by linarith) (hslow ρ hρ h12 h1 him) hr

end GaloisForLFunctions.ArithmeticAuxiliaryDynamics
