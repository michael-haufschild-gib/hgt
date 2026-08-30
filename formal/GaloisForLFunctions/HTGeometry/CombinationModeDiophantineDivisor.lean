import Mathlib

/-!
# Square-summability of a mode-divided datum under a Diophantine condition

For a frequency vector `ℓ` on a finite set of coordinates, a combination mode `m` is divided by the
linear form `m·ℓ`.  If the form obeys a fixed-exponent Diophantine bound `|m·ℓ| ≥ γ·H(m)^{-κ}` in the
mode height `H(m) = max(3, maxᵢ|mᵢ|)`, and the datum has exponentially decaying coefficients, then the
divided datum is square-summable.

The estimate is a product comparison on the integer lattice: the height is at most `3 + |m|₁`, the
weight `3 + Σᵢ aᵢ` is dominated by `∏ᵢ (3 + aᵢ)`, and the exponential weight factors exactly, so the
whole majorant is a finite product of one-dimensional summable weights.
-/

namespace GaloisForLFunctions.HTGeometry

open Finset

theorem summable_natWeight (K : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℕ => (3 + (n : ℝ)) ^ K * r ^ n) := by
  have hnorm : ‖r‖ < 1 := by rwa [Real.norm_eq_abs, abs_of_nonneg hr0]
  have h1 : Summable (fun n : ℕ => (n : ℝ) ^ K * r ^ n) :=
    summable_pow_mul_geometric_of_norm_lt_one K hnorm
  have h2 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_lt_one hr0 hr1
  have hmaj : Summable (fun n : ℕ => (6 : ℝ) ^ K * (r ^ n + (n : ℝ) ^ K * r ^ n)) :=
    (h2.add h1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmaj
  have hrn : (0 : ℝ) ≤ r ^ n := pow_nonneg hr0 n
  have hkey : (3 + (n : ℝ)) ^ K ≤ (6 : ℝ) ^ K * (1 + (n : ℝ) ^ K) := by
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h36 : (3 : ℝ) ^ K ≤ (6 : ℝ) ^ K := pow_le_pow_left₀ (by norm_num) (by norm_num) K
      have h0 : (0 : ℝ) ≤ ((0 : ℕ) : ℝ) ^ K := by positivity
      have h6 : (0 : ℝ) ≤ (6 : ℝ) ^ K := by positivity
      push_cast
      push_cast at h0
      rw [show (3 : ℝ) + 0 = 3 by norm_num]
      nlinarith
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hle : (3 : ℝ) + (n : ℝ) ≤ 6 * (n : ℝ) := by linarith
      have := pow_le_pow_left₀ (by positivity) hle K
      calc (3 + (n : ℝ)) ^ K ≤ (6 * (n : ℝ)) ^ K := this
        _ = (6 : ℝ) ^ K * (n : ℝ) ^ K := by rw [mul_pow]
        _ ≤ (6 : ℝ) ^ K * (1 + (n : ℝ) ^ K) := by
            have : (0 : ℝ) ≤ (6 : ℝ) ^ K := by positivity
            nlinarith [pow_nonneg (le_of_lt (lt_of_lt_of_le zero_lt_one hn1)) K]
  calc (3 + (n : ℝ)) ^ K * r ^ n ≤ ((6 : ℝ) ^ K * (1 + (n : ℝ) ^ K)) * r ^ n := by
        exact mul_le_mul_of_nonneg_right hkey hrn
    _ = (6 : ℝ) ^ K * (r ^ n + (n : ℝ) ^ K * r ^ n) := by ring

theorem summable_intWeight (K : ℕ) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable (fun n : ℤ => (3 + (n.natAbs : ℝ)) ^ K * r ^ n.natAbs) := by
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using summable_natWeight K hr0 hr1
  · simpa using summable_natWeight K hr0 hr1


theorem three_add_sum_le_prod {ι : Type*} [DecidableEq ι] (a : ι → ℝ) :
    ∀ {t : Finset ι}, t.Nonempty → (∀ i ∈ t, 0 ≤ a i) →
      3 + ∑ i ∈ t, a i ≤ ∏ i ∈ t, (3 + a i) := by
  intro t ht
  induction ht using Finset.Nonempty.cons_induction with
  | singleton j => intro _; simp
  | cons j t hj ht ih =>
      intro ha
      have haj : 0 ≤ a j := ha j (by simp)
      have hsub : ∀ i ∈ t, 0 ≤ a i := fun i hi => ha i (by simp [hi])
      have hIH := ih hsub
      have hsum : 0 ≤ ∑ i ∈ t, a i := Finset.sum_nonneg hsub
      rw [Finset.sum_cons, Finset.prod_cons]
      nlinarith

theorem summable_prod_pi : ∀ {s : ℕ} (g : Fin s → ℤ → ℝ), (∀ i n, 0 ≤ g i n) →
    (∀ i, Summable (g i)) → Summable (fun m : Fin s → ℤ => ∏ i, g i (m i)) := by
  intro s
  induction s with
  | zero => intro g _ _; exact summable_of_hasFiniteSupport (Set.toFinite _)
  | succ s ih =>
      intro g hnn hg
      set F : ℤ → ℝ := g 0 with hF
      set G : (Fin s → ℤ) → ℝ := fun m => ∏ i : Fin s, g i.succ (m i) with hG
      have hprod : Summable (fun p : ℤ × (Fin s → ℤ) => F p.1 * G p.2) :=
        Summable.mul_of_nonneg (hg 0)
          (ih (fun i => g i.succ) (fun i n => hnn _ _) (fun i => hg _))
          (fun n => hnn _ _) (fun m => Finset.prod_nonneg fun i _ => hnn _ _)
      have he := (Fin.consEquiv (fun _ : Fin (s + 1) => ℤ)).summable_iff
        (f := fun m : Fin (s + 1) → ℤ => ∏ i, g i (m i))
      rw [← he]
      refine hprod.congr fun p => ?_
      simp only [Function.comp_apply, Fin.consEquiv, Equiv.coe_fn_mk, Fin.prod_univ_succ,
        Fin.cons_zero, Fin.cons_succ, hF, hG]

/-- The `ℓ¹` size of an integer mode. -/
def modeNorm {s : ℕ} (m : Fin s → ℤ) : ℕ := ∑ i, (m i).natAbs

/-- The height of an integer mode, `H(m) = max(3, max_i |m_i|)`. -/
def modeHeight {s : ℕ} (m : Fin s → ℤ) : ℕ := max 3 (univ.sup fun i => (m i).natAbs)

/-- The linear form of a mode against a frequency vector. -/
def modeForm {s : ℕ} (ℓ : Fin s → ℝ) (m : Fin s → ℤ) : ℝ := ∑ i, (m i : ℝ) * ℓ i

theorem modeHeight_le {s : ℕ} (m : Fin s → ℤ) : (modeHeight m : ℝ) ≤ 3 + (modeNorm m : ℝ) := by
  have hsup : (univ.sup fun i => (m i).natAbs) ≤ modeNorm m := by
    refine Finset.sup_le fun i _ => ?_
    exact Finset.single_le_sum (f := fun i => (m i).natAbs) (fun j _ => Nat.zero_le _)
      (Finset.mem_univ i)
  have : modeHeight m ≤ 3 + modeNorm m := max_le (by omega) (by omega)
  exact_mod_cast this

theorem summable_modeWeight (s K : ℕ) {ρ : ℝ} (hρ : 0 < ρ) :
    Summable (fun m : Fin s → ℤ =>
      (3 + (modeNorm m : ℝ)) ^ K * Real.exp (-(2 * ρ) * (modeNorm m : ℝ))) := by
  classical
  set r : ℝ := Real.exp (-(2 * ρ)) with hrdef
  have hr0 : 0 ≤ r := (Real.exp_pos _).le
  have hr1 : r < 1 := by rw [hrdef]; exact Real.exp_lt_one_iff.mpr (by linarith)
  have hexp : ∀ m : Fin s → ℤ,
      Real.exp (-(2 * ρ) * (modeNorm m : ℝ)) = ∏ i, r ^ (m i).natAbs := by
    intro m
    rw [Finset.prod_pow_eq_pow_sum, hrdef, ← Real.exp_nat_mul]
    congr 1
    rw [modeNorm]
    push_cast
    ring
  rcases Nat.eq_zero_or_pos s with hs | hs
  · subst hs; exact summable_of_hasFiniteSupport (Set.toFinite _)
  set g : Fin s → ℤ → ℝ := fun _ n => (3 + (n.natAbs : ℝ)) ^ K * r ^ n.natAbs with hg
  have hmaj : Summable (fun m : Fin s → ℤ => ∏ i, g i (m i)) :=
    summable_prod_pi g (fun i n => by rw [hg]; positivity)
      (fun i => summable_intWeight K hr0 hr1)
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) hmaj
  have hsplit : (∏ i, g i (m i))
      = (∏ i, (3 + ((m i).natAbs : ℝ)) ^ K) * ∏ i, r ^ (m i).natAbs := by
    rw [← Finset.prod_mul_distrib]
  rw [hexp m, hsplit]
  refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => by positivity)
  have hbase : 3 + (modeNorm m : ℝ) ≤ ∏ i, (3 + ((m i).natAbs : ℝ)) := by
    have := three_add_sum_le_prod (ι := Fin s) (a := fun i => ((m i).natAbs : ℝ))
      (t := (univ : Finset (Fin s))) (Finset.univ_nonempty_iff.mpr ⟨⟨0, hs⟩⟩)
      (fun i _ => by positivity)
    refine le_trans (le_of_eq ?_) this
    rw [modeNorm]
    push_cast
    ring
  have h1 : (0 : ℝ) ≤ 3 + (modeNorm m : ℝ) := by positivity
  calc (3 + (modeNorm m : ℝ)) ^ K ≤ (∏ i, (3 + ((m i).natAbs : ℝ))) ^ K :=
        pow_le_pow_left₀ h1 hbase K
    _ = ∏ i, (3 + ((m i).natAbs : ℝ)) ^ K := by rw [Finset.prod_pow]

/-- **Lemma R, positive half.**  If the frequency vector satisfies a fixed-exponent Diophantine
condition and the datum has exponentially decaying coefficients, the mode-divided solution is
square-summable: `Σ_{m ≠ 0} |ĝ(m)|² / (m·ℓ)² < ∞`. -/
theorem summable_modeDivisor_of_diophantine {s : ℕ} (ℓ : Fin s → ℝ) {γ ρ : ℝ}
    (hγ : 0 < γ) (hρ : 0 < ρ) (κ : ℕ)
    (hdioph : ∀ m : Fin s → ℤ, m ≠ 0 → γ / (modeHeight m : ℝ) ^ κ ≤ |modeForm ℓ m|)
    (ĝ : (Fin s → ℤ) → ℂ)
    (hĝ : ∀ m, ‖ĝ m‖ ≤ Real.exp (-ρ * (modeNorm m : ℝ))) :
    Summable (fun m : {m : Fin s → ℤ // m ≠ 0} =>
      ‖ĝ (m : Fin s → ℤ)‖ ^ 2 / (modeForm ℓ (m : Fin s → ℤ)) ^ 2) := by
  have hmaj : Summable (fun m : Fin s → ℤ =>
      (γ⁻¹) ^ 2 * ((3 + (modeNorm m : ℝ)) ^ (2 * κ)
        * Real.exp (-(2 * ρ) * (modeNorm m : ℝ)))) :=
    (summable_modeWeight s (2 * κ) hρ).mul_left _
  refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_) (hmaj.subtype _)
  obtain ⟨m, hm⟩ := m
  have hH3 : (3 : ℝ) ≤ (modeHeight m : ℝ) := by
    have : (3 : ℕ) ≤ modeHeight m := le_max_left _ _
    exact_mod_cast this
  have hHpos : (0 : ℝ) < (modeHeight m : ℝ) := by linarith
  have hlow : γ / (modeHeight m : ℝ) ^ κ ≤ |modeForm ℓ m| := hdioph m hm
  have hlowpos : (0 : ℝ) < γ / (modeHeight m : ℝ) ^ κ := by positivity
  have hsq : (γ / (modeHeight m : ℝ) ^ κ) ^ 2 ≤ (modeForm ℓ m) ^ 2 := by
    rw [← sq_abs (modeForm ℓ m)]
    exact pow_le_pow_left₀ hlowpos.le hlow 2
  have hnum : ‖ĝ m‖ ^ 2 ≤ Real.exp (-(2 * ρ) * (modeNorm m : ℝ)) := by
    have h1 : ‖ĝ m‖ ^ 2 ≤ (Real.exp (-ρ * (modeNorm m : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hĝ m) 2
    have h2 : (Real.exp (-ρ * (modeNorm m : ℝ))) ^ 2
        = Real.exp (-(2 * ρ) * (modeNorm m : ℝ)) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rwa [h2] at h1
  have hstep : ‖ĝ m‖ ^ 2 / (modeForm ℓ m) ^ 2
      ≤ Real.exp (-(2 * ρ) * (modeNorm m : ℝ)) / (γ / (modeHeight m : ℝ) ^ κ) ^ 2 := by
    gcongr
  refine hstep.trans ?_
  have hrewrite : Real.exp (-(2 * ρ) * (modeNorm m : ℝ)) / (γ / (modeHeight m : ℝ) ^ κ) ^ 2
      = (γ⁻¹) ^ 2 * ((modeHeight m : ℝ) ^ (2 * κ)
        * Real.exp (-(2 * ρ) * (modeNorm m : ℝ))) := by
    rw [div_pow, pow_mul]
    field_simp
    ring
  rw [hrewrite]
  have hheight : ((modeHeight m : ℝ)) ^ (2 * κ) ≤ (3 + (modeNorm m : ℝ)) ^ (2 * κ) :=
    pow_le_pow_left₀ hHpos.le (modeHeight_le m) (2 * κ)
  have hexpnn : (0 : ℝ) ≤ Real.exp (-(2 * ρ) * (modeNorm m : ℝ)) := (Real.exp_pos _).le
  exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hheight hexpnn) (by positivity)


end GaloisForLFunctions.HTGeometry
