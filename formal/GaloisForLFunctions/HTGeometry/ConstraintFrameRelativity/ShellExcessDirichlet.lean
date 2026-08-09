import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellRamificationPower

/-!
# The analytic excess of a ramification power event

The level-`r m` shell splits coefficientwise into the image of the level-`m` shell under
`k ↦ k ^ r` and a positive complement.  The image part is exactly the shell indicator restricted
to `r`-th powers, because a member of the level-`r m` shell which is an `r`-th power has its
`r`-th root in the level-`m` shell.  Reindexing the image part along `k ↦ k ^ r` turns its
Dirichlet series into `S_m(r s)`, giving the exact affine decomposition

`S_{r m}(s) = S_m(r s) + C_{m,r}(s)`,   `Re s > 1`,

with `C_{m,r}` the `{0,1}`-valued excess series.  The excess is nonzero: `2^{r m} · 3` lies in the
level-`r m` shell and is not an `r`-th power.
-/

namespace HTGeometry.ConstraintFrameRelativity

open RHTower Complex

open scoped Classical in
/-- The power-image stream: the level-`r m` shell restricted to `r`-th powers. -/
noncomputable def powerImageStream (m r N : ℕ) : ℤ :=
  if IsRPow r N then shellIndicator (r * m) N else 0

open scoped Classical in
/-- The excess stream: the level-`r m` shell restricted to non-`r`-th-powers. -/
noncomputable def excessStream (m r N : ℕ) : ℤ :=
  if IsRPow r N then 0 else shellIndicator (r * m) N

theorem powerImageStream_add_excessStream (m r N : ℕ) :
    powerImageStream m r N + excessStream m r N = shellIndicator (r * m) N := by
  classical
  rw [powerImageStream, excessStream]
  by_cases h : IsRPow r N <;> simp [h]

theorem abs_powerImageStream_le_one (m r N : ℕ) : |powerImageStream m r N| ≤ 1 := by
  classical
  rw [powerImageStream]
  by_cases h : IsRPow r N
  · rw [if_pos h]
    rcases shellIndicator_eq_zero_or_one (r * m) N with h | h <;> simp [h]
  · simp [h]

theorem abs_excessStream_le_one (m r N : ℕ) : |excessStream m r N| ≤ 1 := by
  classical
  rw [excessStream]
  by_cases h : IsRPow r N
  · simp [h]
  · rw [if_neg h]
    rcases shellIndicator_eq_zero_or_one (r * m) N with h' | h' <;> simp [h']

theorem excessStream_zero (m r : ℕ) : excessStream m r 0 = 0 := by
  classical
  rw [excessStream]
  by_cases h : IsRPow r 0 <;> simp [h]

theorem powerImageStream_zero (m r : ℕ) : powerImageStream m r 0 = 0 := by
  classical
  rw [powerImageStream]
  by_cases h : IsRPow r 0 <;> simp [h]

/-- **The image stream is the level-`m` shell.** -/
theorem powerImageStream_pow {m r : ℕ} (hr : r ≠ 0) (k : ℕ) :
    powerImageStream m r (k ^ r) = shellIndicator m k := by
  classical
  rw [powerImageStream, if_pos (isRPow_pow r k), shellIndicator_pow hr]

/-- **The excess is nonzero.**  The witness `2 ^ (r m) · 3` is not an `r`-th power. -/
theorem excessStream_witness {m r : ℕ} (hm : m ≠ 0) (hr : 2 ≤ r) :
    excessStream m r (2 ^ (r * m) * 3) = 1 := by
  classical
  obtain ⟨hshell, hnot⟩ := excess_witness hm hr
  rw [excessStream, if_neg hnot, hshell]

/-! ## The Dirichlet decomposition -/

theorem lSeriesSummable_of_abs_le_one {f : ℕ → ℤ} (hf : ∀ n, |f n| ≤ 1) {s : ℂ}
    (hs : 1 < s.re) : LSeriesSummable (fun n => ((f n : ℤ) : ℂ)) s := by
  refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ => ?_) hs
  have := hf n
  rw [show ‖((f n : ℤ) : ℂ)‖ = |(f n : ℝ)| by
    simp [Complex.norm_intCast]]
  exact_mod_cast this

theorem lSeriesSummable_powerImageStream (m r : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun N => ((powerImageStream m r N : ℤ) : ℂ)) s :=
  lSeriesSummable_of_abs_le_one (abs_powerImageStream_le_one m r) hs

theorem lSeriesSummable_excessStream (m r : ℕ) {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun N => ((excessStream m r N : ℤ) : ℂ)) s :=
  lSeriesSummable_of_abs_le_one (abs_excessStream_le_one m r) hs

/-- Reindexing the image part along `k ↦ k ^ r` dilates the Dirichlet variable. -/
theorem lSeries_powerImageStream {m r : ℕ} (hr : r ≠ 0) (s : ℂ) :
    LSeries (fun N => ((powerImageStream m r N : ℤ) : ℂ)) s
      = LSeries (fun k => ((shellIndicator m k : ℤ) : ℂ)) ((r : ℂ) * s) := by
  classical
  have hinj : Function.Injective fun k : ℕ => k ^ r := Nat.pow_left_injective hr
  have hsupp : Function.support
      (fun N => LSeries.term (fun N => ((powerImageStream m r N : ℤ) : ℂ)) s N)
      ⊆ Set.range fun k : ℕ => k ^ r := by
    intro N hN
    by_contra hrange
    apply hN
    have hnot : ¬ IsRPow r N := by
      rintro ⟨k, rfl⟩
      exact hrange ⟨k, rfl⟩
    have hz : powerImageStream m r N = 0 := by rw [powerImageStream, if_neg hnot]
    rcases eq_or_ne N 0 with rfl | hN0
    · simp [LSeries.term_zero]
    · simp [LSeries.term_of_ne_zero hN0, hz]
  have hterm : ∀ k : ℕ,
      LSeries.term (fun N => ((powerImageStream m r N : ℤ) : ℂ)) s (k ^ r)
        = LSeries.term (fun k => ((shellIndicator m k : ℤ) : ℂ)) ((r : ℂ) * s) k := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [zero_pow hr]
      simp [LSeries.term]
    · have hkr : k ^ r ≠ 0 := pow_ne_zero _ hk
      rw [LSeries.term_of_ne_zero hkr, LSeries.term_of_ne_zero hk, powerImageStream_pow hr]
      congr 1
      rw [Complex.natCast_cpow_natCast_mul]
      norm_cast
  rw [LSeries, LSeries, ← hinj.tsum_eq hsupp]
  exact tsum_congr hterm

/-- **The exact affine excess decomposition.** -/
theorem lSeries_shell_eq_dilate_add_excess {m r : ℕ} (hr : r ≠ 0) {s : ℂ} (hs : 1 < s.re) :
    LSeries (fun N => ((shellIndicator (r * m) N : ℤ) : ℂ)) s
      = LSeries (fun k => ((shellIndicator m k : ℤ) : ℂ)) ((r : ℂ) * s)
        + LSeries (fun N => ((excessStream m r N : ℤ) : ℂ)) s := by
  have hsplit : (fun N => ((shellIndicator (r * m) N : ℤ) : ℂ))
      = (fun N => ((powerImageStream m r N : ℤ) : ℂ))
        + fun N => ((excessStream m r N : ℤ) : ℂ) := by
    funext N
    have := powerImageStream_add_excessStream m r N
    simp only [Pi.add_apply]
    exact_mod_cast congrArg (fun z : ℤ => (z : ℂ)) this.symm
  rw [hsplit, LSeries_add (lSeriesSummable_powerImageStream m r hs)
    (lSeriesSummable_excessStream m r hs), lSeries_powerImageStream hr]

end HTGeometry.ConstraintFrameRelativity
