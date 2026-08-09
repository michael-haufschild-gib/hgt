import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellExcessSupport
import GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.ShellExcessDirichlet

/-!
# The split-defect functor of a ramification power event

On coefficient streams the power event `m ↦ r m` is realised by the pair

`(V_r x)(N) = x(k)` if `N = k^r`, else `0`,   `(R_r y)(k) = y(k^r)`,

which satisfies `R_r V_r = 1`, `V_s V_r = V_{sr}`, `R_r R_s = R_{sr}`.  The shell excess is the
distinguished kernel point `c_{m,r} = a_{rm} - V_r a_m`, and composition obeys the exact crossed
cocycle `c_{m,sr} = V_s c_{m,r} + c_{rm,s}` with disjoint supports.  Hence the affine transports
`T_{m,r}(x) = V_r x + c_{m,r}` compose strictly and carry `a_m` to `a_{rm}`; the depth-dependent
translations `x ↦ x - a_m` conjugate them to the linear maps `V_r`, so the cocycle is a
coboundary and not a curvature.

Two consequences: the Dirichlet series of the excess satisfies the crossed analytic cocycle
`C_{m,sr}(z) = C_{m,r}(sz) + C_{rm,s}(z)`, and every observer that factors through `R_r` is blind
to the excess, while the single coordinate `2^{rm}·3` detects it.
-/

namespace HTGeometry.ConstraintFrameRelativity

open RHTower

/-! ## The `r`-th root -/

open scoped Classical in
/-- The `r`-th root of an `r`-th power; zero elsewhere. -/
noncomputable def rroot (r N : ℕ) : ℕ := if h : IsRPow r N then h.choose else 0

theorem pow_rroot {r N : ℕ} (h : IsRPow r N) : (rroot r N) ^ r = N := by
  classical
  rw [rroot, dif_pos h]
  exact h.choose_spec

theorem rroot_pow {r : ℕ} (hr : r ≠ 0) (k : ℕ) : rroot r (k ^ r) = k :=
  Nat.pow_left_injective hr (pow_rroot (isRPow_pow r k))

/-! ## The extension and restriction operators -/

open scoped Classical in
/-- Extension of a stream to `r`-th-power support. -/
noncomputable def extendPow (r : ℕ) (x : ℕ → ℂ) (N : ℕ) : ℂ :=
  if IsRPow r N then x (rroot r N) else 0

/-- Restriction of a stream along `k ↦ k^r`. -/
def restrictPow (r : ℕ) (y : ℕ → ℂ) (k : ℕ) : ℂ := y (k ^ r)

theorem extendPow_pow {r : ℕ} (hr : r ≠ 0) (x : ℕ → ℂ) (k : ℕ) :
    extendPow r x (k ^ r) = x k := by
  classical
  rw [extendPow, if_pos (isRPow_pow r k), rroot_pow hr]

theorem extendPow_of_not_isRPow {r : ℕ} {N : ℕ} (h : ¬ IsRPow r N) (x : ℕ → ℂ) :
    extendPow r x N = 0 := by
  classical
  rw [extendPow, if_neg h]

theorem restrictPow_extendPow {r : ℕ} (hr : r ≠ 0) (x : ℕ → ℂ) :
    restrictPow r (extendPow r x) = x := by
  funext k
  rw [restrictPow, extendPow_pow hr]

theorem restrictPow_restrictPow (s r : ℕ) (y : ℕ → ℂ) :
    restrictPow r (restrictPow s y) = restrictPow (s * r) y := by
  funext k
  rw [restrictPow, restrictPow, restrictPow, ← pow_mul, mul_comm r s]

theorem extendPow_extendPow {s r : ℕ} (hs : s ≠ 0) (hr : r ≠ 0) (x : ℕ → ℂ) :
    extendPow s (extendPow r x) = extendPow (s * r) x := by
  classical
  funext N
  by_cases hsr : IsRPow (s * r) N
  · obtain ⟨L, rfl⟩ := hsr
    have h1 : (L ^ r) ^ s = L ^ (s * r) := by
      rw [← pow_mul, mul_comm r s]
    rw [← h1, extendPow_pow hs, extendPow_pow hr, h1, extendPow_pow (Nat.mul_ne_zero hs hr)]
  · rw [extendPow_of_not_isRPow hsr]
    by_cases hs' : IsRPow s N
    · obtain ⟨K, rfl⟩ := hs'
      rw [extendPow_pow hs, extendPow_of_not_isRPow]
      exact fun h => hsr ((isRPow_mul_iff_of_pow hs (rfl : K ^ s = K ^ s)).mpr h)
    · rw [extendPow_of_not_isRPow hs']

theorem extendPow_add (r : ℕ) (x y : ℕ → ℂ) :
    extendPow r (x + y) = extendPow r x + extendPow r y := by
  classical
  funext N
  by_cases h : IsRPow r N <;> simp [extendPow, h]

theorem extendPow_sub (r : ℕ) (x y : ℕ → ℂ) :
    extendPow r (x - y) = extendPow r x - extendPow r y := by
  classical
  funext N
  by_cases h : IsRPow r N <;> simp [extendPow, h]

/-! ## The shell streams and their split defect -/

/-- The complex shell stream. -/
noncomputable def shellStream (m n : ℕ) : ℂ := ((shellIndicator m n : ℤ) : ℂ)

/-- The split defect of a power event. -/
noncomputable def shellDefect (m r : ℕ) : ℕ → ℂ :=
  shellStream (r * m) - extendPow r (shellStream m)

/-- **The split defect is the excess stream.** -/
theorem shellDefect_eq_excessStream {m r : ℕ} (hr : r ≠ 0) (N : ℕ) :
    shellDefect m r N = ((excessStream m r N : ℤ) : ℂ) := by
  classical
  by_cases h : IsRPow r N
  · obtain ⟨k, rfl⟩ := h
    rw [shellDefect]
    simp only [Pi.sub_apply]
    rw [extendPow_pow hr, shellStream, shellStream, shellIndicator_pow hr,
      excessStream, if_pos (isRPow_pow r k)]
    simp
  · rw [shellDefect]
    simp only [Pi.sub_apply]
    rw [extendPow_of_not_isRPow h, shellStream, excessStream, if_neg h]
    simp

theorem restrictPow_shellDefect {m r : ℕ} (hr : r ≠ 0) :
    restrictPow r (shellDefect m r) = 0 := by
  funext k
  rw [restrictPow, shellDefect]
  simp only [Pi.sub_apply, Pi.zero_apply]
  rw [extendPow_pow hr, shellStream, shellStream, shellIndicator_pow hr]
  ring

/-- **The crossed excess cocycle.** -/
theorem shellDefect_cocycle {m r s : ℕ} (hs : s ≠ 0) (hr : r ≠ 0) :
    shellDefect m (s * r) = extendPow s (shellDefect m r) + shellDefect (r * m) s := by
  rw [shellDefect, shellDefect, shellDefect, extendPow_sub, extendPow_extendPow hs hr,
    ← mul_assoc]
  abel

/-! ## The affine transport -/

/-- The affine transport of a power event. -/
noncomputable def shellTransport (m r : ℕ) (x : ℕ → ℂ) : ℕ → ℂ :=
  extendPow r x + shellDefect m r

theorem shellTransport_shellStream (m r : ℕ) :
    shellTransport m r (shellStream m) = shellStream (r * m) := by
  rw [shellTransport, shellDefect]
  abel

/-- **Strict composition of affine transports.** -/
theorem shellTransport_comp {m r s : ℕ} (hs : s ≠ 0) (hr : r ≠ 0) (x : ℕ → ℂ) :
    shellTransport (r * m) s (shellTransport m r x) = shellTransport m (s * r) x := by
  rw [shellTransport, shellTransport, shellTransport, extendPow_add, extendPow_extendPow hs hr,
    shellDefect_cocycle hs hr]
  abel

/-- **The cocycle is a coboundary.**  Depth-dependent translation conjugates the affine transport
to the linear extension operator. -/
theorem shellTransport_conjugate {m r : ℕ} (x : ℕ → ℂ) :
    shellTransport m r x - shellStream (r * m) = extendPow r (x - shellStream m) := by
  rw [shellTransport, shellDefect, extendPow_sub]
  abel

/-! ## The kernel decomposition -/

/-- **Kernel splitting.**  A stream killed by `R_{sr}` splits canonically. -/
theorem ker_split {s r : ℕ} (hs : s ≠ 0) {y : ℕ → ℂ} (hy : restrictPow (s * r) y = 0) :
    y = (y - extendPow s (restrictPow s y)) + extendPow s (restrictPow s y)
      ∧ restrictPow s (y - extendPow s (restrictPow s y)) = 0
      ∧ restrictPow r (restrictPow s y) = 0 := by
  refine ⟨by abel, ?_, ?_⟩
  · funext k
    simp only [Pi.sub_apply, Pi.zero_apply, restrictPow]
    rw [extendPow_pow hs]
    simp [restrictPow]
  · rw [restrictPow_restrictPow, hy]

/-! ## The Dirichlet transgression -/

theorem lSeries_extendPow {s : ℕ} (hs : s ≠ 0) (f : ℕ → ℂ) (z : ℂ) :
    LSeries (extendPow s f) z = LSeries f ((s : ℂ) * z) := by
  classical
  have hinj : Function.Injective fun k : ℕ => k ^ s := Nat.pow_left_injective hs
  have hsupp : Function.support (fun N => LSeries.term (extendPow s f) z N)
      ⊆ Set.range fun k : ℕ => k ^ s := by
    intro N hN
    by_contra hrange
    apply hN
    have hnot : ¬ IsRPow s N := by
      rintro ⟨k, rfl⟩
      exact hrange ⟨k, rfl⟩
    rcases eq_or_ne N 0 with rfl | hN0
    · simp [LSeries.term_zero]
    · simp [LSeries.term_of_ne_zero hN0, extendPow_of_not_isRPow hnot]
  have hterm : ∀ k : ℕ,
      LSeries.term (extendPow s f) z (k ^ s) = LSeries.term f ((s : ℂ) * z) k := by
    intro k
    rcases eq_or_ne k 0 with rfl | hk
    · rw [zero_pow hs]
      simp [LSeries.term_zero]
    · have hks : k ^ s ≠ 0 := pow_ne_zero _ hk
      rw [LSeries.term_of_ne_zero hks, LSeries.term_of_ne_zero hk, extendPow_pow hs]
      congr 1
      rw [Complex.natCast_cpow_natCast_mul]
      norm_cast
  rw [LSeries, LSeries, ← hinj.tsum_eq hsupp]
  exact tsum_congr hterm

theorem norm_extendPow_le {s : ℕ} {f : ℕ → ℂ} {C : ℝ} (hC : 0 ≤ C) (hf : ∀ k, ‖f k‖ ≤ C)
    (N : ℕ) : ‖extendPow s f N‖ ≤ C := by
  classical
  by_cases h : IsRPow s N
  · rw [extendPow, if_pos h]
    exact hf _
  · rw [extendPow, if_neg h]
    simpa using hC

theorem norm_excessStream_le_one (m r N : ℕ) : ‖((excessStream m r N : ℤ) : ℂ)‖ ≤ 1 := by
  have h := abs_excessStream_le_one m r N
  rw [show ‖((excessStream m r N : ℤ) : ℂ)‖ = |((excessStream m r N : ℤ) : ℝ)| by
    simp [Complex.norm_intCast]]
  exact_mod_cast h

theorem lSeriesSummable_extendPow_excessStream (m r s : ℕ) {z : ℂ} (hz : 1 < z.re) :
    LSeriesSummable (extendPow s (fun N => ((excessStream m r N : ℤ) : ℂ))) z :=
  LSeriesSummable_of_bounded_of_one_lt_re (m := 1)
    (fun n _ => norm_extendPow_le zero_le_one (norm_excessStream_le_one m r) n) hz

/-- **The crossed analytic cocycle.** -/
theorem lSeries_shellDefect_cocycle {m r s : ℕ} (hs : s ≠ 0) (hr : r ≠ 0) {z : ℂ}
    (hz : 1 < z.re) :
    LSeries (fun N => ((excessStream m (s * r) N : ℤ) : ℂ)) z
      = LSeries (fun N => ((excessStream m r N : ℤ) : ℂ)) ((s : ℂ) * z)
        + LSeries (fun N => ((excessStream (r * m) s N : ℤ) : ℂ)) z := by
  have hfun : (fun N => ((excessStream m (s * r) N : ℤ) : ℂ))
      = extendPow s (fun N => ((excessStream m r N : ℤ) : ℂ))
        + fun N => ((excessStream (r * m) s N : ℤ) : ℂ) := by
    funext N
    have h1 := shellDefect_cocycle (m := m) hs hr
    have h2 : shellDefect m (s * r) N
        = extendPow s (shellDefect m r) N + shellDefect (r * m) s N := by
      rw [h1]
      rfl
    rw [shellDefect_eq_excessStream (Nat.mul_ne_zero hs hr) N,
      shellDefect_eq_excessStream hs N] at h2
    have h3 : extendPow s (shellDefect m r) N
        = extendPow s (fun N => ((excessStream m r N : ℤ) : ℂ)) N := by
      classical
      by_cases h : IsRPow s N
      · obtain ⟨k, rfl⟩ := h
        rw [extendPow_pow hs, extendPow_pow hs, shellDefect_eq_excessStream hr]
      · rw [extendPow_of_not_isRPow h, extendPow_of_not_isRPow h]
    rw [h3] at h2
    simpa using h2
  rw [hfun, LSeries_add (lSeriesSummable_extendPow_excessStream m r s hz)
    (lSeriesSummable_excessStream (r * m) s hz), lSeries_extendPow hs]

/-! ## Blindness of inherited observers -/

/-- **The power-diagonal observer factors through the root retraction.** -/
theorem powerDiagonal_factors (r m : ℕ) (y : ℕ → ℂ) (k : ℕ) :
    y (k ^ (r * m)) = restrictPow r y (k ^ m) := by
  rw [restrictPow, ← pow_mul, mul_comm m r]

/-- **Blindness.**  A stream supported off the `r`-th powers is invisible to the power diagonal. -/
theorem powerDiagonal_blind {r : ℕ} {y : ℕ → ℂ} (hy : ∀ N, IsRPow r N → y N = 0) (m k : ℕ) :
    y (k ^ (r * m)) = 0 :=
  hy _ ⟨k ^ m, by rw [← pow_mul, mul_comm m r]⟩

theorem shellDefect_isRPow_zero {m r : ℕ} (hr : r ≠ 0) {N : ℕ} (h : IsRPow r N) :
    shellDefect m r N = 0 := by
  obtain ⟨k, rfl⟩ := h
  have := restrictPow_shellDefect (m := m) hr
  have h2 : restrictPow r (shellDefect m r) k = 0 := by rw [this]; rfl
  simpa [restrictPow] using h2

/-- **A single coordinate detects the excess.** -/
theorem shellDefect_witness {m r : ℕ} (hm : m ≠ 0) (hr : 2 ≤ r) :
    shellDefect m r (2 ^ (r * m) * 3) = 1 := by
  rw [shellDefect_eq_excessStream (by omega) , excessStream_witness hm hr]
  norm_num

end HTGeometry.ConstraintFrameRelativity
