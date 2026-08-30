import Mathlib

/-!
# Dirichlet's box principle for a linear form

Among the `(N+1)^s` integer vectors with entries in `{0, …, N}` two give values of a nonnegative
linear form inside one of `(N+1)^s − 1` equal boxes, so their difference is a nonzero integer vector
with entries bounded by `N` on which the form is smaller than the box length.  This is the
elementary no-go behind "the infinite base is the obstruction": with the support size `s` free, no
fixed-exponent Diophantine condition can hold.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

/-- Two nonnegative reals in `[0, K·b]` with the same clamped box index differ by at most `b`. -/
theorem sub_le_of_min_floor_eq {b x y : ℝ} (hb : 0 < b) {K : ℕ} (hK : 0 < K)
    (hx : 0 ≤ x) (hyM : y ≤ (K : ℝ) * b) (hxy : x ≤ y)
    (h : min ⌊x / b⌋₊ (K - 1) = min ⌊y / b⌋₊ (K - 1)) : y - x ≤ b := by
  have hy : 0 ≤ y := le_trans hx hxy
  have hxdiv : 0 ≤ x / b := div_nonneg hx hb.le
  have hydiv : 0 ≤ y / b := div_nonneg hy hb.le
  have hkx : ((min ⌊x / b⌋₊ (K - 1) : ℕ) : ℝ) * b ≤ x := by
    have h1 : ((min ⌊x / b⌋₊ (K - 1) : ℕ) : ℝ) ≤ x / b :=
      le_trans (by exact_mod_cast min_le_left ⌊x / b⌋₊ (K - 1)) (Nat.floor_le hxdiv)
    calc ((min ⌊x / b⌋₊ (K - 1) : ℕ) : ℝ) * b ≤ (x / b) * b :=
          mul_le_mul_of_nonneg_right h1 hb.le
      _ = x := by field_simp
  by_cases hcase : ⌊y / b⌋₊ ≤ K - 1
  · rw [min_eq_left hcase] at h
    rw [h] at hkx
    have h2 : y / b < (⌊y / b⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : y < ((⌊y / b⌋₊ : ℝ) + 1) * b := by
      calc y = (y / b) * b := by field_simp
        _ < ((⌊y / b⌋₊ : ℝ) + 1) * b := mul_lt_mul_of_pos_right h2 hb
    nlinarith
  · push Not at hcase
    rw [min_eq_right (by omega : K - 1 ≤ ⌊y / b⌋₊)] at h
    rw [h] at hkx
    have hyK : (K : ℝ) * b ≤ y := by
      have h1 : ((K : ℕ) : ℝ) ≤ y / b :=
        le_trans (by exact_mod_cast (show K ≤ ⌊y / b⌋₊ by omega)) (Nat.floor_le hydiv)
      calc (K : ℝ) * b ≤ (y / b) * b := mul_le_mul_of_nonneg_right h1 hb.le
        _ = y := by field_simp
    have hcast : ((K - 1 : ℕ) : ℝ) = (K : ℝ) - 1 := by
      have h1 : (1 : ℕ) ≤ K := hK
      push_cast [Nat.cast_sub h1]
      ring
    rw [hcast] at hkx
    nlinarith

/-- **Dirichlet's box principle for a nonnegative linear form.** -/
theorem exists_small_linear_form {s : ℕ} (hs : 0 < s) (ℓ : Fin s → ℝ) (hℓ : ∀ i, 0 ≤ ℓ i)
    {N : ℕ} (hN : 0 < N) :
    ∃ m : Fin s → ℤ, m ≠ 0 ∧ (∀ i, |m i| ≤ (N : ℤ)) ∧
      |∑ i, (m i : ℝ) * ℓ i| ≤ ((N : ℝ) * ∑ i, ℓ i) / (((N + 1) ^ s : ℕ) - 1) := by
  classical
  set K : ℕ := (N + 1) ^ s - 1 with hKdef
  have hpow : 2 ≤ (N + 1) ^ s := by
    have h1 : (N + 1) ^ 1 ≤ (N + 1) ^ s := Nat.pow_le_pow_right (by omega) hs
    simp only [pow_one] at h1
    omega
  have hK : 0 < K := by omega
  set L : ℝ := ∑ i, ℓ i with hL
  have hLnn : 0 ≤ L := Finset.sum_nonneg fun i _ => hℓ i
  rcases eq_or_lt_of_le hLnn with hL0 | hLpos
  · refine ⟨fun i => if i = ⟨0, hs⟩ then 1 else 0, ?_, ?_, ?_⟩
    · intro h
      have := congrFun h ⟨0, hs⟩
      simp at this
    · intro i
      by_cases hi : i = ⟨0, hs⟩
      · simp [hi]
        omega
      · simp [hi]
    · have hzero : ∀ i, ℓ i = 0 := by
        intro i
        by_contra hne
        have hpos : 0 < ℓ i := lt_of_le_of_ne (hℓ i) (Ne.symm hne)
        have : 0 < L := by
          rw [hL]
          exact Finset.sum_pos' (fun j _ => hℓ j) ⟨i, Finset.mem_univ i, hpos⟩
        rw [← hL0] at this
        exact lt_irrefl 0 this
      simp [hzero, ← hL0]
  · set b : ℝ := ((N : ℝ) * L) / (K : ℝ) with hb
    have hbpos : 0 < b := by
      rw [hb]
      have : (0 : ℝ) < N := by exact_mod_cast hN
      positivity
    set g : (Fin s → Fin (N + 1)) → ℝ := fun a => ∑ i, ((a i : ℕ) : ℝ) * ℓ i with hg
    have hgnn : ∀ a, 0 ≤ g a := fun a =>
      Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hℓ i)
    have hgM : ∀ a, g a ≤ (K : ℝ) * b := by
      intro a
      have hKb : (K : ℝ) * b = (N : ℝ) * L := by
        rw [hb]
        field_simp
      rw [hKb, hL, Finset.mul_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      refine mul_le_mul_of_nonneg_right ?_ (hℓ i)
      have := (a i).isLt
      exact_mod_cast Nat.lt_succ_iff.1 this
    have hcard : Fintype.card (Fin K) < Fintype.card (Fin s → Fin (N + 1)) := by
      simp only [Fintype.card_fin, Fintype.card_fun, Fintype.card_fin]
      omega
    obtain ⟨a, a', hne, heq⟩ := Fintype.exists_ne_map_eq_of_card_lt
      (fun a : Fin s → Fin (N + 1) => (⟨min ⌊g a / b⌋₊ (K - 1), by omega⟩ : Fin K)) hcard
    have hidx : min ⌊g a / b⌋₊ (K - 1) = min ⌊g a' / b⌋₊ (K - 1) := by
      have := congrArg Fin.val heq
      simpa using this
    refine ⟨fun i => ((a i : ℕ) : ℤ) - ((a' i : ℕ) : ℤ), ?_, ?_, ?_⟩
    · intro h
      refine hne (funext fun i => ?_)
      have hi := congrFun h i
      simp only [Pi.zero_apply, sub_eq_zero] at hi
      exact Fin.ext (by exact_mod_cast hi)
    · intro i
      have h1 := Nat.lt_succ_iff.1 (a i).isLt
      have h2 := Nat.lt_succ_iff.1 (a' i).isLt
      rw [abs_le]
      constructor <;> [skip; skip] <;> push_cast <;> omega
    · have hsum : ∑ i, ((((a i : ℕ) : ℤ) - ((a' i : ℕ) : ℤ) : ℤ) : ℝ) * ℓ i = g a - g a' := by
        rw [hg, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        push_cast
        ring
      rw [hsum]
      have hbeq : b = ((N : ℝ) * L) / (((N + 1) ^ s : ℕ) - 1) := by
        rw [hb, hKdef]
        congr 1
        have : ((N + 1) ^ s : ℕ) - 1 = (((N + 1) ^ s - 1 : ℕ) : ℝ) := by
          push_cast [Nat.cast_sub (by omega : 1 ≤ (N + 1) ^ s)]
          ring
        rw [this]
      rw [← hbeq, abs_le]
      rcases le_total (g a) (g a') with hle | hle
      · constructor
        · nlinarith [sub_le_of_min_floor_eq hbpos hK (hgnn a) (hgM a') hle hidx]
        · nlinarith [sub_le_of_min_floor_eq hbpos hK (hgnn a) (hgM a') hle hidx]
      · constructor
        · nlinarith [sub_le_of_min_floor_eq hbpos hK (hgnn a') (hgM a) hle hidx.symm]
        · nlinarith [sub_le_of_min_floor_eq hbpos hK (hgnn a') (hgM a) hle hidx.symm]


/-- **No fixed-exponent Diophantine bound survives an unbounded support.**  If the partial sums of a
nonnegative sequence grow subexponentially, then modes with entries bounded by `2` make the linear
form arbitrarily small, so no inequality `|m·ℓ| ≥ γ·H(m)^{-κ}` can hold with the support size free. -/
theorem exists_small_mode_of_subexponential {ℓ : ℕ → ℝ} (hℓ : ∀ i, 0 ≤ ℓ i)
    (hgrow : Filter.Tendsto (fun s : ℕ => (∑ i ∈ Finset.range s, ℓ i) / ((3 : ℝ) ^ s - 1))
      Filter.atTop (nhds 0)) {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : ℕ) (m : Fin s → ℤ), 0 < s ∧ m ≠ 0 ∧ (∀ i, |m i| ≤ 2) ∧
      |∑ i, (m i : ℝ) * ℓ (i : ℕ)| < ε := by
  have hhalf : (0 : ℝ) < ε / 2 := by linarith
  have hev := (hgrow.eventually (gt_mem_nhds hhalf)).and (Filter.eventually_ge_atTop 1)
  obtain ⟨s, hsmall, hs1⟩ := hev.exists
  have hs : 0 < s := hs1
  obtain ⟨m, hm0, hmbound, hmsmall⟩ :=
    exists_small_linear_form hs (fun i : Fin s => ℓ (i : ℕ)) (fun i => hℓ _) (N := 2) (by omega)
  refine ⟨s, m, hs, hm0, fun i => by exact_mod_cast hmbound i, ?_⟩
  have hsum : ∑ i : Fin s, ℓ (i : ℕ) = ∑ i ∈ Finset.range s, ℓ i := by
    rw [Finset.sum_range fun i => ℓ i]
  have hcast : (((2 + 1) ^ s : ℕ) : ℝ) - 1 = (3 : ℝ) ^ s - 1 := by
    push_cast
    ring
  rw [hsum, hcast] at hmsmall
  have hden : (0 : ℝ) < (3 : ℝ) ^ s - 1 := by
    have h1 : (3 : ℝ) ^ 1 ≤ (3 : ℝ) ^ s := by
      refine pow_le_pow_right₀ (by norm_num) hs
    simp only [pow_one] at h1
    linarith
  have hkey : ((2 : ℝ) * ∑ i ∈ Finset.range s, ℓ i) / ((3 : ℝ) ^ s - 1) < ε := by
    rw [mul_div_assoc]
    linarith [hsmall]
  exact lt_of_le_of_lt hmsmall hkey

/-- The negative Diophantine statement in the shape used by the card: for every `γ > 0` and every
exponent `κ`, some bounded-entry mode violates `|m·ℓ| ≥ γ·H(m)^{-κ}` with `H(m) = 3`. -/
theorem not_polynomially_diophantine {ℓ : ℕ → ℝ} (hℓ : ∀ i, 0 ≤ ℓ i)
    (hgrow : Filter.Tendsto (fun s : ℕ => (∑ i ∈ Finset.range s, ℓ i) / ((3 : ℝ) ^ s - 1))
      Filter.atTop (nhds 0)) {γ : ℝ} (hγ : 0 < γ) (κ : ℕ) :
    ∃ (s : ℕ) (m : Fin s → ℤ), 0 < s ∧ m ≠ 0 ∧ (∀ i, |m i| ≤ 2) ∧
      |∑ i, (m i : ℝ) * ℓ (i : ℕ)| < γ * (3 : ℝ) ^ (-(κ : ℤ)) :=
  exists_small_mode_of_subexponential hℓ hgrow (by positivity)

end GaloisForLFunctions.HTGeometry
