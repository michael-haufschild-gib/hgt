/-
# Cantor filled Julia sets for `‖c‖ ≥ 4`, elementarily (B1e, first class)

Total disconnectedness of `K_c` for `‖c‖ ≥ 4`, with no Branner–Hubbard moduli and no
hyperbolicity: every `z ∈ K_c` satisfies `‖z−u‖·‖z+u‖ = ‖f_c z‖ ≤ √(2‖c‖)` for a fixed square
root `u` of `−c`, and since `‖z−u‖ + ‖z+u‖ ≥ 2‖u‖ = 2√‖c‖`, each `K`-point lies within `√2` of
exactly one of `±u` — a metric two-cell partition, clopen in `K`.  Two points of a preconnected
subset share the cell at every iterate, and on a shared cell the map expands:
`‖f a − f b‖ = ‖a−b‖·‖a+b‖ ≥ (2‖u‖ − 2√2)·‖a−b‖ ≥ (11/10)·‖a−b‖`.  Iterating against the
uniform bound `diam K ≤ 2‖c‖` forces the two points to coincide.  This is the disconnected-lane
class that will make mixed pairs `(c₁ ∈ (−2,0) real, ‖c₂‖ ≥ 4)` fully unconditional once the
steering wiring (#110) lands.  Axiom-clean.
-/
import GaloisForLFunctions.Bottcher.Dynamics
import Mathlib.Analysis.SpecialFunctions.Complex.Log

open Set Metric Topology

namespace Bottcher

/-- **`K_c` is totally disconnected for `‖c‖ ≥ 4`** — the elementary two-cell expansion
argument. -/
theorem isTotallyDisconnected_filledJulia_of_four_le {c : ℂ} (hc : 4 ≤ ‖c‖) :
    IsTotallyDisconnected (filledJulia c) := by
  classical
  -- a square root of `−c`
  have hcne : (-c : ℂ) ≠ 0 := by
    intro h
    rw [neg_eq_zero] at h
    rw [h, norm_zero] at hc
    linarith
  obtain ⟨u, hu⟩ : ∃ u : ℂ, u ^ (2 : ℕ) = -c := by
    refine ⟨Complex.exp (Complex.log (-c) / 2), ?_⟩
    rw [← Complex.exp_nat_mul]
    rw [show ((2 : ℕ) : ℂ) * (Complex.log (-c) / 2) = Complex.log (-c) by push_cast; ring]
    exact Complex.exp_log hcne
  have hu2 : ‖u‖ ^ (2 : ℕ) = ‖c‖ := by rw [← norm_pow, hu, norm_neg]
  have huge : 2 ≤ ‖u‖ := by nlinarith [norm_nonneg u]
  have hsqrt2 : Real.sqrt 2 ^ (2 : ℕ) = 2 := Real.sq_sqrt (by norm_num)
  have hsqrt2nn : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hsqrt2lt : Real.sqrt 2 < 2 := by nlinarith
  -- membership bounds
  have hKnorm : ∀ z ∈ filledJulia c, ‖z‖ ≤ ‖c‖ := by
    intro z hz
    have h1 := filledJulia_subset_closedBall c hz
    rw [Metric.mem_closedBall, dist_zero_right] at h1
    calc ‖z‖ ≤ max 2 ‖c‖ := h1
      _ = ‖c‖ := max_eq_right (by linarith)
  have hK2 : ∀ z ∈ filledJulia c, ‖z‖ ^ (2 : ℕ) ≤ 2 * ‖c‖ := by
    intro z hz
    have hfz : quadratic c z ∈ filledJulia c := (mem_filledJulia_iff_quadratic_mem c z).mp hz
    have h1 : ‖quadratic c z‖ ≤ ‖c‖ := hKnorm _ hfz
    rw [quadratic_apply] at h1
    calc ‖z‖ ^ (2 : ℕ) = ‖z ^ (2 : ℕ)‖ := (norm_pow z 2).symm
      _ = ‖(z ^ (2 : ℕ) + c) - c‖ := by ring_nf
      _ ≤ ‖z ^ (2 : ℕ) + c‖ + ‖c‖ := norm_sub_le _ _
      _ ≤ ‖c‖ + ‖c‖ := by linarith
      _ = 2 * ‖c‖ := by ring
  -- the fibre-product identity and the two-cell dichotomy
  have hprod : ∀ z ∈ filledJulia c, ‖z - u‖ * ‖z + u‖ ≤ Real.sqrt 2 * ‖u‖ := by
    intro z hz
    have hfz : quadratic c z ∈ filledJulia c := (mem_filledJulia_iff_quadratic_mem c z).mp hz
    have h1 : ‖quadratic c z‖ ^ (2 : ℕ) ≤ 2 * ‖c‖ := hK2 _ hfz
    have h2 : ‖quadratic c z‖ ≤ Real.sqrt (2 * ‖c‖) :=
      (Real.le_sqrt (norm_nonneg _) (by positivity)).mpr h1
    have h3 : Real.sqrt (2 * ‖c‖) = Real.sqrt 2 * ‖u‖ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2), ← hu2, Real.sqrt_sq (norm_nonneg u)]
    calc ‖z - u‖ * ‖z + u‖ = ‖(z - u) * (z + u)‖ := (norm_mul _ _).symm
      _ = ‖quadratic c z‖ := by
          rw [quadratic_apply]
          congr 1
          have hcu : c = -(u ^ (2 : ℕ)) := by rw [hu]; ring
          rw [hcu]
          ring
      _ ≤ Real.sqrt 2 * ‖u‖ := h3 ▸ h2
  have hsum : ∀ z : ℂ, 2 * ‖u‖ ≤ ‖z - u‖ + ‖z + u‖ := by
    intro z
    have h1 : (2 : ℂ) * u = (z + u) - (z - u) := by ring
    calc 2 * ‖u‖ = ‖(2 : ℂ) * u‖ := by rw [norm_mul]; norm_num
      _ = ‖(z + u) - (z - u)‖ := by rw [h1]
      _ ≤ ‖z + u‖ + ‖z - u‖ := norm_sub_le _ _
      _ = ‖z - u‖ + ‖z + u‖ := by ring
  have hcell : ∀ z ∈ filledJulia c, ‖z - u‖ ≤ Real.sqrt 2 ∨ ‖z + u‖ ≤ Real.sqrt 2 := by
    intro z hz
    have hpq := hprod z hz
    have hs := hsum z
    have hupos : (0 : ℝ) < ‖u‖ := by linarith
    rcases le_total (‖z - u‖) (‖z + u‖) with hle | hle
    · left
      have hq : ‖u‖ ≤ ‖z + u‖ := by linarith
      have h2 : ‖z - u‖ * ‖u‖ ≤ Real.sqrt 2 * ‖u‖ := by
        calc ‖z - u‖ * ‖u‖ ≤ ‖z - u‖ * ‖z + u‖ :=
              mul_le_mul_of_nonneg_left hq (norm_nonneg _)
          _ ≤ Real.sqrt 2 * ‖u‖ := hpq
      exact le_of_mul_le_mul_right h2 hupos
    · right
      have hq : ‖u‖ ≤ ‖z - u‖ := by linarith
      have h2 : ‖z + u‖ * ‖u‖ ≤ Real.sqrt 2 * ‖u‖ := by
        calc ‖z + u‖ * ‖u‖ ≤ ‖z - u‖ * ‖z + u‖ := by
              nlinarith [norm_nonneg (z + u)]
          _ ≤ Real.sqrt 2 * ‖u‖ := hpq
      exact le_of_mul_le_mul_right h2 hupos
  -- preconnected subsets of `K` live in one cell
  have hKsplit : ∀ t' : Set ℂ, t' ⊆ filledJulia c → IsPreconnected t' →
      (∀ x ∈ t', ‖x - u‖ ≤ Real.sqrt 2) ∨ (∀ x ∈ t', ‖x + u‖ ≤ Real.sqrt 2) := by
    intro t' ht'K ht'c
    set Up : Set ℂ := {z | dist z u < dist z (-u)} with hUpdef
    set Um : Set ℂ := {z | dist z (-u) < dist z u} with hUmdef
    have hUpo : IsOpen Up := isOpen_lt (continuous_id.dist continuous_const)
      (continuous_id.dist continuous_const)
    have hUmo : IsOpen Um := isOpen_lt (continuous_id.dist continuous_const)
      (continuous_id.dist continuous_const)
    have hdistu : ∀ z : ℂ, dist z u = ‖z - u‖ := fun z => dist_eq_norm z u
    have hdistmu : ∀ z : ℂ, dist z (-u) = ‖z + u‖ := fun z => by
      rw [dist_eq_norm, sub_neg_eq_add]
    have hcellUp : ∀ z ∈ filledJulia c, z ∈ Up → ‖z - u‖ ≤ Real.sqrt 2 := by
      intro z hz hzU
      rcases hcell z hz with h | h
      · exact h
      · exfalso
        have hzU' : ‖z - u‖ < ‖z + u‖ := by
          have := hzU
          rwa [hUpdef, Set.mem_setOf_eq, hdistu, hdistmu] at this
        have hs := hsum z
        linarith
    have hcellUm : ∀ z ∈ filledJulia c, z ∈ Um → ‖z + u‖ ≤ Real.sqrt 2 := by
      intro z hz hzU
      rcases hcell z hz with h | h
      · exfalso
        have hzU' : ‖z + u‖ < ‖z - u‖ := by
          have := hzU
          rwa [hUmdef, Set.mem_setOf_eq, hdistmu, hdistu] at this
        have hs := hsum z
        linarith
      · exact h
    have hKsub : ∀ z ∈ filledJulia c, z ∈ Up ∪ Um := by
      intro z hz
      have hs := hsum z
      rcases hcell z hz with h | h
      · left
        show dist z u < dist z (-u)
        rw [hdistu, hdistmu]
        linarith
      · right
        show dist z (-u) < dist z u
        rw [hdistu, hdistmu]
        linarith
    by_cases hUpall : t' ⊆ Up
    · exact Or.inl fun x hx => hcellUp x (ht'K hx) (hUpall hx)
    · have hUmall : t' ⊆ Um := by
        by_contra hUmnot
        obtain ⟨x, hxt, hxUp⟩ := not_subset.mp hUpall
        obtain ⟨y, hyt, hyUm⟩ := not_subset.mp hUmnot
        have hxUm : x ∈ Um := (hKsub x (ht'K hxt)).resolve_left hxUp
        have hyUp : y ∈ Up := (hKsub y (ht'K hyt)).resolve_right hyUm
        obtain ⟨p, hp⟩ := ht'c Up Um hUpo hUmo (fun a ha => hKsub a (ht'K ha))
          ⟨y, hyt, hyUp⟩ ⟨x, hxt, hxUm⟩
        have h1 : dist p u < dist p (-u) := hp.2.1
        have h2 : dist p (-u) < dist p u := hp.2.2
        exact lt_asymm h1 h2
      exact Or.inr fun x hx => hcellUm x (ht'K hx) (hUmall hx)
  -- one-step expansion on a shared cell
  have hstep : ∀ a ∈ filledJulia c, ∀ b ∈ filledJulia c,
      ((‖a - u‖ ≤ Real.sqrt 2 ∧ ‖b - u‖ ≤ Real.sqrt 2) ∨
       (‖a + u‖ ≤ Real.sqrt 2 ∧ ‖b + u‖ ≤ Real.sqrt 2)) →
      (11 / 10 : ℝ) * ‖a - b‖ ≤ ‖quadratic c a - quadratic c b‖ := by
    intro a _ b _ hcase
    have hfab : ‖quadratic c a - quadratic c b‖ = ‖a - b‖ * ‖a + b‖ := by
      rw [quadratic_apply, quadratic_apply, ← norm_mul]
      congr 1
      ring
    have hab : (11 / 10 : ℝ) ≤ ‖a + b‖ := by
      rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h3 : (2 : ℂ) * u = (a + b) - ((a - u) + (b - u)) := by ring
        have h4 : 2 * ‖u‖ ≤ ‖a + b‖ + (‖a - u‖ + ‖b - u‖) := by
          calc 2 * ‖u‖ = ‖(2 : ℂ) * u‖ := by rw [norm_mul]; norm_num
            _ = ‖(a + b) - ((a - u) + (b - u))‖ := by rw [h3]
            _ ≤ ‖a + b‖ + ‖(a - u) + (b - u)‖ := norm_sub_le _ _
            _ ≤ ‖a + b‖ + (‖a - u‖ + ‖b - u‖) := by
                linarith [norm_add_le (a - u) (b - u)]
        nlinarith
      · have h3 : (2 : ℂ) * u = ((a + u) + (b + u)) - (a + b) := by ring
        have h4 : 2 * ‖u‖ ≤ (‖a + u‖ + ‖b + u‖) + ‖a + b‖ := by
          calc 2 * ‖u‖ = ‖(2 : ℂ) * u‖ := by rw [norm_mul]; norm_num
            _ = ‖((a + u) + (b + u)) - (a + b)‖ := by rw [h3]
            _ ≤ ‖(a + u) + (b + u)‖ + ‖a + b‖ := norm_sub_le _ _
            _ ≤ (‖a + u‖ + ‖b + u‖) + ‖a + b‖ := by
                linarith [norm_add_le (a + u) (b + u)]
        nlinarith
    rw [hfab]
    calc (11 / 10 : ℝ) * ‖a - b‖ = ‖a - b‖ * (11 / 10) := by ring
      _ ≤ ‖a - b‖ * ‖a + b‖ := mul_le_mul_of_nonneg_left hab (norm_nonneg (a - b))
  -- the diagonal argument
  intro t hts htc z hz w hw
  by_contra hne
  have hzw : (0 : ℝ) < ‖z - w‖ := by
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr hne
  have hqc : Continuous (quadratic c) := by
    unfold quadratic
    fun_prop
  have key : ∀ n : ℕ, ((11 : ℝ) / 10) ^ n * ‖z - w‖
      ≤ ‖(quadratic c)^[n] z - (quadratic c)^[n] w‖ := by
    intro n
    induction n with
    | zero => simp
    | succ m ih =>
        have ht'c : IsPreconnected ((quadratic c)^[m] '' t) :=
          htc.image _ (hqc.iterate m).continuousOn
        have ht'K : (quadratic c)^[m] '' t ⊆ filledJulia c := by
          rintro _ ⟨x, hx, rfl⟩
          exact filledJulia_forward (hts hx) m
        have hmz : (quadratic c)^[m] z ∈ (quadratic c)^[m] '' t := ⟨z, hz, rfl⟩
        have hmw : (quadratic c)^[m] w ∈ (quadratic c)^[m] '' t := ⟨w, hw, rfl⟩
        have hcase : (‖(quadratic c)^[m] z - u‖ ≤ Real.sqrt 2 ∧
              ‖(quadratic c)^[m] w - u‖ ≤ Real.sqrt 2) ∨
            (‖(quadratic c)^[m] z + u‖ ≤ Real.sqrt 2 ∧
              ‖(quadratic c)^[m] w + u‖ ≤ Real.sqrt 2) := by
          rcases hKsplit _ ht'K ht'c with h | h
          · exact Or.inl ⟨h _ hmz, h _ hmw⟩
          · exact Or.inr ⟨h _ hmz, h _ hmw⟩
        rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
        calc ((11 : ℝ) / 10) ^ (m + 1) * ‖z - w‖
            = (11 / 10) * (((11 : ℝ) / 10) ^ m * ‖z - w‖) := by ring
          _ ≤ (11 / 10) * ‖(quadratic c)^[m] z - (quadratic c)^[m] w‖ :=
              mul_le_mul_of_nonneg_left ih (by norm_num)
          _ ≤ ‖quadratic c ((quadratic c)^[m] z) - quadratic c ((quadratic c)^[m] w)‖ :=
              hstep _ (ht'K hmz) _ (ht'K hmw) hcase
  have hbd : ∀ n : ℕ, ‖(quadratic c)^[n] z - (quadratic c)^[n] w‖ ≤ 2 * ‖c‖ := by
    intro n
    have h1 := hKnorm _ (filledJulia_forward (hts hz) n)
    have h2 := hKnorm _ (filledJulia_forward (hts hw) n)
    calc ‖(quadratic c)^[n] z - (quadratic c)^[n] w‖
        ≤ ‖(quadratic c)^[n] z‖ + ‖(quadratic c)^[n] w‖ := norm_sub_le _ _
      _ ≤ 2 * ‖c‖ := by linarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt ((2 * ‖c‖) / ‖z - w‖)
    (by norm_num : (1 : ℝ) < 11 / 10)
  have h1 := key n
  have h2 := hbd n
  rw [div_lt_iff₀ hzw] at hn
  linarith

end Bottcher
