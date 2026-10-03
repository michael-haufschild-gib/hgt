import GaloisForLFunctions.RHTower.Sieve.VinogradovBilinearExplicitSaving
import GaloisForLFunctions.RHTower.Sieve.VinogradovLogTaylorRemainder

/-!
# From the sum `Σ n^{it}` to logarithmic bilinear sums

Shifting `n ↦ n - h` with `h = (Q+l)(Q+m)`, `0 ≤ l, m < Q`, moves an interval sum of
`n^{it} = e((t/2π) log n)` by at most `2h` terms, and
`(x - h)^{it} = x^{it} e((t/2π) log(1 - h/x))`.  Averaging over the `Q²` shifts gives

`Q² ‖Σ_{A < n ≤ A+L} n^{it}‖ ≤ Σ_{A < x ≤ A+L} ‖R(t, x, Q)‖ + 8Q⁴`,
`R(t, x, Q) = Σ_{l,m < Q} e((t/2π) log(1 - (Q+l)(Q+m)/x))`

whenever `4Q² ≤ A` (`sq_mul_norm_sum_logPhase_le`).  Each `R(t, x, Q)` is a bilinear sum in
`(Q+l)(Q+m)` after Taylor expansion of the logarithm.

The coefficients of that expansion are small positive reals; `a/q = 1/⌊1/α⌋` approximates `α` to
within `1/q²` (`exists_unit_fraction_approx`).
-/

namespace RHTower.Sieve

open scoped BigOperators

noncomputable section

/-- **Unit-fraction approximation.** For `0 < α ≤ 1`, `q = ⌊1/α⌋` has `|α - 1/q| ≤ 1/q²`. -/
theorem exists_unit_fraction_approx {α : ℝ} (hα0 : 0 < α) (hα1 : α ≤ 1) :
    ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ 1 / α ∧ 1 / α < q + 1 ∧
      |α - (1 : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ (2 : ℕ) := by
  set y := 1 / α with hy
  have hy1 : 1 ≤ y := by rw [hy, le_div_iff₀ hα0]; linarith
  refine ⟨⌊y⌋₊, Nat.floor_pos.mpr hy1, Nat.floor_le (by linarith), Nat.lt_floor_add_one y, ?_⟩
  set q := ⌊y⌋₊
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.floor_pos.mpr hy1
  have hq0 : (0 : ℝ) < q := by linarith
  have hqy : (q : ℝ) ≤ y := Nat.floor_le (by linarith)
  have hyq : y < q + 1 := Nat.lt_floor_add_one y
  have hαy : α = 1 / y := by rw [hy]; field_simp
  have hupper : α ≤ 1 / q := by
    rw [hαy]; exact one_div_le_one_div_of_le hq0 hqy
  have hlower : 1 / ((q : ℝ) + 1) < α := by
    rw [hαy]; exact one_div_lt_one_div_of_lt (by linarith) hyq
  rw [abs_of_nonpos (by linarith)]
  have h : 1 / (q : ℝ) - 1 / ((q : ℝ) + 1) ≤ 1 / (q : ℝ) ^ 2 := by
    rw [div_sub_div _ _ hq0.ne' (by linarith), div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  linarith

/-- Moving an interval sum of unimodular terms by `h ≤ A` changes it by at most `2h`. -/
theorem norm_sum_Ioc_sub_sum_Ioc_shift_le (g : ℕ → ℂ) (hg : ∀ n, ‖g n‖ ≤ 1) {A L h : ℕ}
    (hh : h ≤ A) :
    ‖∑ n ∈ Finset.Ioc A (A + L), g n - ∑ n ∈ Finset.Ioc (A - h) (A + L - h), g n‖ ≤
      2 * (h : ℝ) := by
  have hprefix : ∀ {a b : ℕ}, a ≤ b →
      ∑ n ∈ Finset.Ioc a b, g n = ∑ n ∈ Finset.Ioc 0 b, g n - ∑ n ∈ Finset.Ioc 0 a, g n := by
    intro a b hab
    rw [← Finset.sum_Ioc_consecutive g (Nat.zero_le a) hab]
    ring
  have hblock : ∀ {m : ℕ}, h ≤ m →
      ‖∑ n ∈ Finset.Ioc 0 m, g n - ∑ n ∈ Finset.Ioc 0 (m - h), g n‖ ≤ h := by
    intro m hm
    rw [← hprefix (Nat.sub_le m h)]
    calc ‖∑ n ∈ Finset.Ioc (m - h) m, g n‖ ≤ ∑ n ∈ Finset.Ioc (m - h) m, ‖g n‖ :=
          norm_sum_le _ _
      _ ≤ ∑ _n ∈ Finset.Ioc (m - h) m, (1 : ℝ) := Finset.sum_le_sum fun n _ => hg n
      _ = h := by
          rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one]
          congr 1
          omega
  rw [hprefix (by omega : A ≤ A + L), hprefix (by omega : A - h ≤ A + L - h)]
  have h1 := hblock (m := A + L) (by omega)
  have h2 := hblock (m := A) hh
  have e : A + L - h = (A + L) - h := rfl
  calc ‖∑ n ∈ Finset.Ioc 0 (A + L), g n - ∑ n ∈ Finset.Ioc 0 A, g n -
        (∑ n ∈ Finset.Ioc 0 (A + L - h), g n - ∑ n ∈ Finset.Ioc 0 (A - h), g n)‖
      = ‖(∑ n ∈ Finset.Ioc 0 (A + L), g n - ∑ n ∈ Finset.Ioc 0 (A + L - h), g n) -
          (∑ n ∈ Finset.Ioc 0 A, g n - ∑ n ∈ Finset.Ioc 0 (A - h), g n)‖ := by
        congr 1; ring
    _ ≤ ‖∑ n ∈ Finset.Ioc 0 (A + L), g n - ∑ n ∈ Finset.Ioc 0 (A + L - h), g n‖ +
          ‖∑ n ∈ Finset.Ioc 0 A, g n - ∑ n ∈ Finset.Ioc 0 (A - h), g n‖ := norm_sub_le _ _
    _ ≤ h + h := add_le_add h1 h2
    _ = 2 * (h : ℝ) := by ring

/-- The logarithmic phase `n^{it} = e((t/2π) log n)`. -/
def vinogradovLogPhase (t : ℝ) (n : ℕ) : ℂ :=
  finitePhaseChar (t / (2 * Real.pi) * Real.log n)

theorem norm_vinogradovLogPhase (t : ℝ) (n : ℕ) : ‖vinogradovLogPhase t n‖ = 1 :=
  norm_finitePhaseChar _

/-- `(x - h)^{it} = x^{it} e((t/2π) log(1 - h/x))` for `h < x`. -/
theorem vinogradovLogPhase_sub {t : ℝ} {x h : ℕ} (hhx : h < x) :
    vinogradovLogPhase t (x - h) =
      vinogradovLogPhase t x * finitePhaseChar (t / (2 * Real.pi) * Real.log (1 - h / x)) := by
  unfold vinogradovLogPhase
  rw [← finitePhaseChar_add]
  congr 1
  have hx0 : (0 : ℝ) < x := by exact_mod_cast (lt_of_le_of_lt (Nat.zero_le h) hhx)
  have hhxR : (h : ℝ) < x := by exact_mod_cast hhx
  have h1 : (0 : ℝ) < 1 - h / x := by
    rw [sub_pos, div_lt_one hx0]; exact hhxR
  have hcast : ((x - h : ℕ) : ℝ) = (x : ℝ) * (1 - h / x) := by
    rw [Nat.cast_sub hhx.le]
    field_simp
  rw [hcast, Real.log_mul hx0.ne' h1.ne']
  ring

/-- **Shift averaging.** `Q² ‖Σ_{A<n≤A+L} n^{it}‖ ≤ Σ_{A<x≤A+L} ‖R(t,x,Q)‖ + 8Q⁴` for
`4Q² ≤ A`. -/
theorem sq_mul_norm_sum_logPhase_le {t : ℝ} {A L Q : ℕ} (hA : 4 * Q ^ 2 ≤ A) :
    (Q : ℝ) ^ 2 * ‖∑ n ∈ Finset.Ioc A (A + L), vinogradovLogPhase t n‖ ≤
      ∑ x ∈ Finset.Ioc A (A + L), ‖routeTLogRatioBilinearSum t (x : ℝ) Q‖ +
        8 * (Q : ℝ) ^ 4 := by
  classical
  set S := ∑ n ∈ Finset.Ioc A (A + L), vinogradovLogPhase t n with hS
  set hh : Fin Q → Fin Q → ℕ := fun l m => (Q + l.val) * (Q + m.val) with hhdef
  have hhle : ∀ l m, hh l m < 4 * Q ^ 2 := by
    intro l m
    simp only [hhdef]
    have hl := l.isLt
    have hm := m.isLt
    calc (Q + l.val) * (Q + m.val) < (2 * Q) * (2 * Q) :=
          Nat.mul_lt_mul'' (by omega) (by omega)
      _ = 4 * Q ^ 2 := by ring
  -- the shifted sums
  set T : Fin Q → Fin Q → ℂ := fun l m =>
    ∑ x ∈ Finset.Ioc A (A + L), vinogradovLogPhase t (x - hh l m) with hTdef
  have hTreindex : ∀ l m, T l m =
      ∑ n ∈ Finset.Ioc (A - hh l m) (A + L - hh l m), vinogradovLogPhase t n := by
    intro l m
    have hle : hh l m ≤ A := le_trans (hhle l m).le hA
    have hmap := Finset.map_add_right_Ioc (A - hh l m) (A + L - hh l m) (hh l m)
    have e1 : A - hh l m + hh l m = A := Nat.sub_add_cancel hle
    have e2 : A + L - hh l m + hh l m = A + L := Nat.sub_add_cancel (by omega)
    rw [e1, e2] at hmap
    simp only [hTdef]
    rw [← hmap, Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n _
    simp
  have hdiff : ∀ l m, ‖S - T l m‖ ≤ 8 * (Q : ℝ) ^ 2 := by
    intro l m
    rw [hTreindex]
    have hle : hh l m ≤ A := le_trans (hhle l m).le hA
    have h := norm_sum_Ioc_sub_sum_Ioc_shift_le (vinogradovLogPhase t)
      (fun n => (norm_vinogradovLogPhase t n).le) (L := L) hle
    have hhR : (hh l m : ℝ) ≤ 4 * (Q : ℝ) ^ 2 := by exact_mod_cast (hhle l m).le
    linarith
  -- the main term
  have hmain : ∑ l : Fin Q, ∑ m : Fin Q, T l m =
      ∑ x ∈ Finset.Ioc A (A + L),
        vinogradovLogPhase t x * routeTLogRatioBilinearSum t (x : ℝ) Q := by
    have hpt : ∀ x ∈ Finset.Ioc A (A + L),
        vinogradovLogPhase t x * routeTLogRatioBilinearSum t (x : ℝ) Q =
          ∑ l : Fin Q, ∑ m : Fin Q, vinogradovLogPhase t (x - hh l m) := by
      intro x hx
      have hxA : A < x := (Finset.mem_Ioc.mp hx).1
      unfold routeTLogRatioBilinearSum
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      have hlt : hh l m < x := lt_of_lt_of_le (hhle l m) (le_trans hA hxA.le)
      rw [vinogradovLogPhase_sub hlt]
      congr 3
      simp only [hhdef, vinogradovUpperHalfProduct]
      push_cast
      ring
    calc ∑ l : Fin Q, ∑ m : Fin Q, T l m
        = ∑ l : Fin Q, ∑ m : Fin Q, ∑ x ∈ Finset.Ioc A (A + L),
            vinogradovLogPhase t (x - hh l m) := rfl
      _ = ∑ l : Fin Q, ∑ x ∈ Finset.Ioc A (A + L), ∑ m : Fin Q,
            vinogradovLogPhase t (x - hh l m) :=
          Finset.sum_congr rfl fun l _ => Finset.sum_comm
      _ = ∑ x ∈ Finset.Ioc A (A + L), ∑ l : Fin Q, ∑ m : Fin Q,
            vinogradovLogPhase t (x - hh l m) := Finset.sum_comm
      _ = _ := Finset.sum_congr rfl fun x hx => (hpt x hx).symm
  have hmain_norm : ‖∑ l : Fin Q, ∑ m : Fin Q, T l m‖ ≤
      ∑ x ∈ Finset.Ioc A (A + L), ‖routeTLogRatioBilinearSum t (x : ℝ) Q‖ := by
    rw [hmain]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x _ => ?_)
    rw [norm_mul, norm_vinogradovLogPhase, one_mul]
  have hsplit : ((Q : ℂ) ^ 2) * S =
      ∑ l : Fin Q, ∑ m : Fin Q, T l m + ∑ l : Fin Q, ∑ m : Fin Q, (S - T l m) := by
    rw [← Finset.sum_add_distrib]
    simp_rw [← Finset.sum_add_distrib, add_sub_cancel]
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have herr : ‖∑ l : Fin Q, ∑ m : Fin Q, (S - T l m)‖ ≤ 8 * (Q : ℝ) ^ 4 := by
    calc ‖∑ l : Fin Q, ∑ m : Fin Q, (S - T l m)‖
        ≤ ∑ l : Fin Q, ∑ m : Fin Q, ‖S - T l m‖ := by
          refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => norm_sum_le _ _)
      _ ≤ ∑ _l : Fin Q, ∑ _m : Fin Q, 8 * (Q : ℝ) ^ 2 :=
          Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ => hdiff l m
      _ = 8 * (Q : ℝ) ^ 4 := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          ring
  have hnorm : (Q : ℝ) ^ 2 * ‖S‖ = ‖((Q : ℂ) ^ 2) * S‖ := by
    rw [norm_mul, norm_pow, Complex.norm_natCast]
  rw [hnorm, hsplit]
  calc ‖∑ l : Fin Q, ∑ m : Fin Q, T l m + ∑ l : Fin Q, ∑ m : Fin Q, (S - T l m)‖
      ≤ ‖∑ l : Fin Q, ∑ m : Fin Q, T l m‖ + ‖∑ l : Fin Q, ∑ m : Fin Q, (S - T l m)‖ :=
        norm_add_le _ _
    _ ≤ _ := add_le_add hmain_norm herr

end

end RHTower.Sieve
