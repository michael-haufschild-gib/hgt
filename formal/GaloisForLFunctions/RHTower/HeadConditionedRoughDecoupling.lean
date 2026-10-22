import GaloisForLFunctions.RHTower.SteinhausSmoothRoughSplit
import GaloisForLFunctions.RHTower.Sieve.DirichletMVT

/-!
# Head-conditioned decoupling of rough Dirichlet polynomials on the height line

A probe built from the primes below `y` reads the heights through the phases `p^{iτ}`, `p ≤ y`; a
Dirichlet polynomial carried by `y`-rough integers reads them through the phases `m^{iτ}`,
`p ∣ m ⇒ p > y`.  On the prime torus with Haar measure the two blocks of coordinates are
independent, so a weight depending on the head cannot change the second moment of the rough part.
This module proves the same factorisation for the **actual height line**, with an effective error.

* **The mean value theorem at arbitrary integer frequencies**
  (`norm_integral_normSq_familyHeightPoly_sub_diag_le`).  For a finite family `f : ι → ℂ` carried
  by *distinct* positive integers `k q ≤ N`,
  `|∫_0^T |Σ_q f q (k q)^{iτ}|² dτ − T Σ_q |f q|²| ≤ 4N(1 + log N) Σ_q |f q|²`.
  The corpus owns this for the consecutive range `1, …, N`; distinct integer frequencies are the
  form every arithmetic application needs.
* **The decoupling** (`norm_integral_normSq_smooth_mul_rough_sub_diag_le`).  For a head probe
  `P(τ) = Σ_{s ∈ S} w_s s^{iτ}` on `y`-smooth integers and a rough polynomial
  `D(τ) = Σ_{m ∈ M} α_m m^{iτ}`,
  `|∫_0^T |P|²|D|² dτ − T (Σ_s |w_s|²)(Σ_m |α_m|²)| ≤ 4N(1 + log N)(Σ_s |w_s|²)(Σ_m |α_m|²)`,
  `N` any bound for the products `s·m`.  The diagonal factorises exactly: no head weight of any
  shape sees the rough mean square.
* **The conditioned mean square** (`tendsto_headWeighted_roughMeanSquare`).  The head-weighted mean
  square of `D` converges to its unweighted mean square `Σ_m |α_m|²`.  Weighting the heights by any
  head probe — in particular by one concentrated on the heights where the primes below `y` return
  to a prescribed phase — leaves the rough second moment unchanged.

Two arithmetic inputs carry the whole statement, and both are specific to `ℕ`: the frequency
`log(s'n) − log(sm)` of a cross term vanishes **only** on the diagonal, because a product of a
smooth and a rough integer determines both factors; and when it does not vanish it is bounded away
from `0` by `1/max(s'n, sm)`, because distinct integers differ by at least one.  In a Beurling
system the first survives and the second fails: products of generators are not integers and the
off-diagonal frequencies can be arbitrarily small.  So the effective error is the integrality of
the frequencies, not their independence.
-/

namespace RHTower

open Finset MeasureTheory Filter Topology

noncomputable section

/-! ### 1. Dirichlet polynomials at integer frequencies -/

/-- The Dirichlet polynomial of a finite family `f : ι → ℂ` carried by the integer frequencies
`k : ι → ℕ`: `F(τ) = Σ_{q ∈ A} f q · (k q)^{iτ}`. -/
def familyHeightPoly {ι : Type*} (A : Finset ι) (k : ι → ℕ) (f : ι → ℂ) (τ : ℝ) : ℂ :=
  ∑ q ∈ A, f q * Complex.exp (((τ * Real.log (k q) : ℝ) : ℂ) * Complex.I)

/-- The Dirichlet polynomial carried by a finite set of integers: `Σ_{n ∈ A} f n · n^{iτ}`. -/
def integerHeightPoly (A : Finset ℕ) (f : ℕ → ℂ) (τ : ℝ) : ℂ :=
  familyHeightPoly A id f τ

/-- The coefficient of the integer `i + 1` in a family carried by integer frequencies. -/
def familyFibreCoeff {ι : Type*} [DecidableEq ι] (A : Finset ι) (k : ι → ℕ) (f : ι → ℂ)
    (i : ℕ) : ℂ :=
  ∑ q ∈ A with k q - 1 = i, f q

/-- A family at distinct integer frequencies is the Dirichlet polynomial of its fibre
coefficients. -/
theorem familyHeightPoly_eq_dirPoly {ι : Type*} [DecidableEq ι] {A : Finset ι} {k : ι → ℕ}
    {f : ι → ℂ} {N : ℕ} (hk0 : ∀ q ∈ A, 0 < k q) (hkN : ∀ q ∈ A, k q ≤ N) (τ : ℝ) :
    familyHeightPoly A k f τ
      = Sieve.dirPoly N (fun j : Fin N => familyFibreCoeff A k f (j : ℕ)) τ := by
  have hmaps : ∀ q ∈ A, k q - 1 ∈ Finset.range N := by
    intro q hq
    have h0 := hk0 q hq
    have hN := hkN q hq
    exact Finset.mem_range.mpr (by omega)
  -- the fibre sums, with the phase of the fibre pulled out
  have hfib : ∀ i ∈ Finset.range N,
      familyFibreCoeff A k f i * Complex.exp (((τ * Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * Complex.I)
        = ∑ q ∈ A with k q - 1 = i,
            f q * Complex.exp (((τ * Real.log (k q) : ℝ) : ℂ) * Complex.I) := by
    intro i _
    rw [familyFibreCoeff, Finset.sum_mul]
    refine Finset.sum_congr rfl fun q hq => ?_
    obtain ⟨hqA, hqi⟩ := Finset.mem_filter.mp hq
    have h0 := hk0 q hqA
    have hkq : k q = i + 1 := by omega
    have hcast : ((k q : ℝ)) = (i : ℝ) + 1 := by simp [hkq]
    rw [hcast]
  calc familyHeightPoly A k f τ
      = ∑ i ∈ Finset.range N, ∑ q ∈ A with k q - 1 = i,
          f q * Complex.exp (((τ * Real.log (k q) : ℝ) : ℂ) * Complex.I) :=
        (Finset.sum_fiberwise_of_maps_to hmaps _).symm
    _ = ∑ i ∈ Finset.range N,
          familyFibreCoeff A k f i *
            Complex.exp (((τ * Real.log ((i : ℝ) + 1) : ℝ) : ℂ) * Complex.I) :=
        (Finset.sum_congr rfl hfib).symm
    _ = Sieve.dirPoly N (fun j : Fin N => familyFibreCoeff A k f (j : ℕ)) τ := by
        rw [Sieve.dirPoly, Fin.sum_univ_eq_sum_range
          (fun i : ℕ => familyFibreCoeff A k f i *
            Complex.exp (((τ * Real.log ((i : ℕ) + 1) : ℝ) : ℂ) * Complex.I)) N]

/-- At distinct integer frequencies every fibre holds at most one index, so the square of a fibre
coefficient is the sum of the squares over the fibre. -/
theorem normSq_familyFibreCoeff {ι : Type*} [DecidableEq ι] {A : Finset ι} {k : ι → ℕ} {f : ι → ℂ}
    (hk0 : ∀ q ∈ A, 0 < k q) (hinj : ∀ q ∈ A, ∀ q' ∈ A, k q = k q' → q = q') (i : ℕ) :
    ‖familyFibreCoeff A k f i‖ ^ 2 = ∑ q ∈ A with k q - 1 = i, ‖f q‖ ^ 2 := by
  rcases Finset.eq_empty_or_nonempty (A.filter fun q => k q - 1 = i) with h | ⟨q₀, hq₀⟩
  · rw [familyFibreCoeff, h, Finset.sum_empty]
    simp
  · have hsing : (A.filter fun q => k q - 1 = i) = {q₀} := by
      obtain ⟨hq₀A, hq₀i⟩ := Finset.mem_filter.mp hq₀
      refine Finset.eq_singleton_iff_unique_mem.mpr ⟨hq₀, fun q hq => ?_⟩
      obtain ⟨hqA, hqi⟩ := Finset.mem_filter.mp hq
      have h1 := hk0 q hqA
      have h2 := hk0 q₀ hq₀A
      exact hinj q hqA q₀ hq₀A (by omega)
    rw [familyFibreCoeff, hsing, Finset.sum_singleton, Finset.sum_singleton]

/-- **The mean value theorem at arbitrary integer frequencies.** For a finite family carried by
distinct positive integers `k q ≤ N`,
`|∫_0^T |Σ_q f q (k q)^{iτ}|² dτ − T Σ_q |f q|²| ≤ 4N(1 + log N) Σ_q |f q|²`. -/
theorem norm_integral_normSq_familyHeightPoly_sub_diag_le {ι : Type*} [DecidableEq ι]
    {A : Finset ι} {k : ι → ℕ} {f : ι → ℂ} {N : ℕ} (T : ℝ)
    (hk0 : ∀ q ∈ A, 0 < k q) (hkN : ∀ q ∈ A, k q ≤ N)
    (hinj : ∀ q ∈ A, ∀ q' ∈ A, k q = k q' → q = q') :
    |(∫ τ in (0 : ℝ)..T, ‖familyHeightPoly A k f τ‖ ^ 2) - T * ∑ q ∈ A, ‖f q‖ ^ 2|
      ≤ 4 * (N : ℝ) * (1 + Real.log N) * ∑ q ∈ A, ‖f q‖ ^ 2 := by
  have hmaps : ∀ q ∈ A, k q - 1 ∈ Finset.range N := by
    intro q hq
    have h0 := hk0 q hq
    have hN := hkN q hq
    exact Finset.mem_range.mpr (by omega)
  have hdiag : ∑ j : Fin N, ‖familyFibreCoeff A k f (j : ℕ)‖ ^ 2 = ∑ q ∈ A, ‖f q‖ ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => ‖familyFibreCoeff A k f i‖ ^ 2) N]
    have hstep : ∑ i ∈ Finset.range N, ‖familyFibreCoeff A k f i‖ ^ 2
        = ∑ i ∈ Finset.range N, ∑ q ∈ A with k q - 1 = i, ‖f q‖ ^ 2 :=
      Finset.sum_congr rfl fun i _ => normSq_familyFibreCoeff (f := f) hk0 hinj i
    rw [hstep]
    exact Finset.sum_fiberwise_of_maps_to hmaps _
  have hpoly : ∀ τ : ℝ, familyHeightPoly A k f τ
      = Sieve.dirPoly N (fun j : Fin N => familyFibreCoeff A k f (j : ℕ)) τ :=
    fun τ => familyHeightPoly_eq_dirPoly hk0 hkN τ
  have hbase := Sieve.dirichlet_meanValue_theorem N
    (fun j : Fin N => familyFibreCoeff A k f (j : ℕ)) T
  rw [hdiag] at hbase
  simpa only [hpoly] using hbase

/-! ### 2. The head probe decouples from the rough polynomial -/

/-- A smooth head probe times a rough polynomial is the family polynomial at the product
frequencies. -/
theorem integerHeightPoly_mul_eq_familyHeightPoly {S M : Finset ℕ} {w α : ℕ → ℂ}
    (hS : ∀ s ∈ S, s ≠ 0) (hM : ∀ m ∈ M, m ≠ 0) (τ : ℝ) :
    integerHeightPoly S w τ * integerHeightPoly M α τ
      = familyHeightPoly (S ×ˢ M) (fun q => q.1 * q.2) (fun q => w q.1 * α q.2) τ := by
  have hterm : ∀ s ∈ S, ∀ m ∈ M,
      (w s * Complex.exp (((τ * Real.log s : ℝ) : ℂ) * Complex.I)) *
        (α m * Complex.exp (((τ * Real.log m : ℝ) : ℂ) * Complex.I))
      = (w s * α m) * Complex.exp (((τ * Real.log ((s * m : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I) := by
    intro s hs m hm
    have hs0 : ((s : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (hS s hs)
    have hm0 : ((m : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (hM m hm)
    have hlog : Real.log ((s * m : ℕ) : ℝ) = Real.log s + Real.log m := by
      push_cast
      exact Real.log_mul hs0 hm0
    rw [hlog, show ((τ * (Real.log s + Real.log m) : ℝ) : ℂ) * Complex.I
        = ((τ * Real.log s : ℝ) : ℂ) * Complex.I + ((τ * Real.log m : ℝ) : ℂ) * Complex.I by
          push_cast; ring, Complex.exp_add]
    ring
  simp only [integerHeightPoly, familyHeightPoly, id_eq]
  rw [Finset.sum_mul_sum, Finset.sum_product]
  exact Finset.sum_congr rfl fun s hs => Finset.sum_congr rfl fun m hm => hterm s hs m hm

/-- **Head-conditioned decoupling on the height line.** For a probe `P` carried by `y`-smooth
integers and a Dirichlet polynomial `D` carried by `y`-rough integers,
`|∫_0^T |P|²|D|² − T (Σ|w|²)(Σ|α|²)| ≤ 4N(1 + log N)(Σ|w|²)(Σ|α|²)`, for any bound `N` on the
products.  The diagonal factorises: the head weight does not change the rough mean square. -/
theorem norm_integral_normSq_smooth_mul_rough_sub_diag_le {y : ℕ} {S M : Finset ℕ} {w α : ℕ → ℂ}
    {N : ℕ} (T : ℝ)
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers y)
    (hM0 : ∀ m ∈ M, m ≠ 0) (hMr : ∀ m ∈ M, ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m)
    (hN : ∀ s ∈ S, ∀ m ∈ M, s * m ≤ N) :
    |(∫ τ in (0 : ℝ)..T, ‖integerHeightPoly S w τ‖ ^ 2 * ‖integerHeightPoly M α τ‖ ^ 2)
        - T * ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑ m ∈ M, ‖α m‖ ^ 2)|
      ≤ 4 * (N : ℝ) * (1 + Real.log N) *
          ((∑ s ∈ S, ‖w s‖ ^ 2) * ∑ m ∈ M, ‖α m‖ ^ 2) := by
  classical
  have hS0 : ∀ s ∈ S, s ≠ 0 := fun s hs => Nat.ne_zero_of_mem_smoothNumbers (hS s hs)
  set A : Finset (ℕ × ℕ) := S ×ˢ M with hA
  set k : ℕ × ℕ → ℕ := fun q => q.1 * q.2 with hk
  set f : ℕ × ℕ → ℂ := fun q => w q.1 * α q.2 with hf
  have hmem : ∀ q ∈ A, q.1 ∈ S ∧ q.2 ∈ M := fun q hq => Finset.mem_product.mp hq
  have hk0 : ∀ q ∈ A, 0 < k q := by
    intro q hq
    obtain ⟨h1, h2⟩ := hmem q hq
    exact Nat.mul_pos (Nat.pos_of_ne_zero (hS0 _ h1)) (Nat.pos_of_ne_zero (hM0 _ h2))
  have hkN : ∀ q ∈ A, k q ≤ N := by
    intro q hq
    obtain ⟨h1, h2⟩ := hmem q hq
    exact hN _ h1 _ h2
  have hinj : ∀ q ∈ A, ∀ q' ∈ A, k q = k q' → q = q' := by
    intro q hq q' hq' heq
    obtain ⟨h1, h2⟩ := hmem q hq
    obtain ⟨h1', h2'⟩ := hmem q' hq'
    obtain ⟨he1, he2⟩ := smooth_rough_pair_unique (hS _ h1) (hM0 _ h2) (hMr _ h2)
      (hS _ h1') (hM0 _ h2') (hMr _ h2') heq
    exact Prod.ext he1 he2
  have hdiag : ∑ q ∈ A, ‖f q‖ ^ 2 = (∑ s ∈ S, ‖w s‖ ^ 2) * ∑ m ∈ M, ‖α m‖ ^ 2 := by
    rw [hA, Finset.sum_product, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun m _ => ?_
    simp [hf, mul_pow]
  have hprod : ∀ τ : ℝ, ‖integerHeightPoly S w τ‖ ^ 2 * ‖integerHeightPoly M α τ‖ ^ 2
      = ‖familyHeightPoly A k f τ‖ ^ 2 := by
    intro τ
    rw [← integerHeightPoly_mul_eq_familyHeightPoly hS0 hM0 τ, norm_mul, mul_pow]
  have hbase := norm_integral_normSq_familyHeightPoly_sub_diag_le (A := A) (k := k) (f := f)
    (N := N) T hk0 hkN hinj
  rw [hdiag] at hbase
  simpa only [hprod] using hbase

/-! ### 3. The conditioned mean square -/

/-- The trivial rough polynomial: `M = {1}` with unit coefficient is the constant `1`. -/
theorem integerHeightPoly_one : integerHeightPoly {1} (fun _ => 1) = fun _ : ℝ => 1 := by
  funext τ
  simp [integerHeightPoly, familyHeightPoly]

/-- `1` is rough at every level: no prime divides it. -/
theorem one_rough (y : ℕ) : ∀ p ∈ Nat.primesBelow y, ¬ p ∣ (1 : ℕ) := by
  intro p hp hdvd
  exact (Nat.prime_of_mem_primesBelow hp).one_lt.ne' (Nat.dvd_one.mp hdvd)

/-- The mean square of a head probe alone, with the same effective error. -/
theorem norm_integral_normSq_head_sub_diag_le {y : ℕ} {S : Finset ℕ} {w : ℕ → ℂ} {N : ℕ} (T : ℝ)
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers y) (hN : ∀ s ∈ S, s ≤ N) :
    |(∫ τ in (0 : ℝ)..T, ‖integerHeightPoly S w τ‖ ^ 2) - T * ∑ s ∈ S, ‖w s‖ ^ 2|
      ≤ 4 * (N : ℝ) * (1 + Real.log N) * ∑ s ∈ S, ‖w s‖ ^ 2 := by
  have hbase := norm_integral_normSq_smooth_mul_rough_sub_diag_le (y := y) (S := S) (M := {1})
    (w := w) (α := fun _ => 1) (N := N) T hS
    (by intro m hm; simp at hm; omega)
    (by intro m hm; simp at hm; subst hm; exact one_rough y)
    (by intro s hs m hm; simp at hm; subst hm; simpa using hN s hs)
  simpa [integerHeightPoly_one] using hbase

/-- **The head-weighted rough mean square is the rough mean square.** Weighting the heights by the
square modulus of any probe built from the primes below `y` — in particular by one concentrated on
the heights at which those primes return to a prescribed phase — leaves the mean square of a
`y`-rough Dirichlet polynomial unchanged. -/
theorem tendsto_headWeighted_roughMeanSquare {y : ℕ} {S M : Finset ℕ} {w α : ℕ → ℂ} {N : ℕ}
    (hS : ∀ s ∈ S, s ∈ Nat.smoothNumbers y)
    (hM0 : ∀ m ∈ M, m ≠ 0) (hMr : ∀ m ∈ M, ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m)
    (hNS : ∀ s ∈ S, s ≤ N) (hN : ∀ s ∈ S, ∀ m ∈ M, s * m ≤ N)
    (hw : 0 < ∑ s ∈ S, ‖w s‖ ^ 2) :
    Tendsto (fun T : ℝ =>
        (∫ τ in (0 : ℝ)..T, ‖integerHeightPoly S w τ‖ ^ 2 * ‖integerHeightPoly M α τ‖ ^ 2) /
          (∫ τ in (0 : ℝ)..T, ‖integerHeightPoly S w τ‖ ^ 2))
      atTop (𝓝 (∑ m ∈ M, ‖α m‖ ^ 2)) := by
  set Sw : ℝ := ∑ s ∈ S, ‖w s‖ ^ 2 with hSw
  set Sα : ℝ := ∑ m ∈ M, ‖α m‖ ^ 2 with hSα
  set C : ℝ := 4 * (N : ℝ) * (1 + Real.log N) with hC
  -- both integrals are `T` times their diagonal up to one absolute constant
  have hnum : ∀ T : ℝ,
      |(∫ τ in (0 : ℝ)..T, ‖integerHeightPoly S w τ‖ ^ 2 * ‖integerHeightPoly M α τ‖ ^ 2)
        - T * (Sw * Sα)| ≤ C * (Sw * Sα) := fun T =>
    norm_integral_normSq_smooth_mul_rough_sub_diag_le T hS hM0 hMr hN
  have hden : ∀ T : ℝ,
      |(∫ τ in (0 : ℝ)..T, ‖integerHeightPoly S w τ‖ ^ 2) - T * Sw| ≤ C * Sw := fun T =>
    norm_integral_normSq_head_sub_diag_le T hS hNS
  have hC0 : 0 ≤ C := by
    have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    positivity
  have hSw0 : 0 ≤ Sw := Finset.sum_nonneg fun _ _ => by positivity
  have hSα0 : 0 ≤ Sα := Finset.sum_nonneg fun _ _ => by positivity
  -- hence the normalised integrals converge to their diagonals
  have key : ∀ (D : ℝ) (I : ℝ → ℝ), 0 ≤ D → (∀ T : ℝ, |I T - T * D| ≤ C * D) →
      Tendsto (fun T : ℝ => I T / T) atTop (𝓝 D) := by
    intro D I hD hI
    rw [Metric.tendsto_atTop]
    intro ε hε
    refine ⟨max 1 ((C * D + 1) / ε), fun T hT => ?_⟩
    have hT1 : (1 : ℝ) ≤ T := le_trans (le_max_left _ _) hT
    have hT0 : 0 < T := lt_of_lt_of_le zero_lt_one hT1
    have hTge : (C * D + 1) / ε ≤ T := le_trans (le_max_right _ _) hT
    have hdist : dist (I T / T) D = |I T - T * D| / T := by
      have hsub : I T / T - D = (I T - T * D) / T := by
        field_simp
      rw [Real.dist_eq, hsub, abs_div, abs_of_pos hT0]
    rw [hdist]
    have hεT : C * D + 1 ≤ ε * T := by
      rw [div_le_iff₀ hε] at hTge
      linarith
    calc |I T - T * D| / T ≤ (C * D) / T := by gcongr; exact hI T
      _ < ε := by
          rw [div_lt_iff₀ hT0]
          nlinarith
  have h1 := key (Sw * Sα) _ (mul_nonneg hSw0 hSα0) hnum
  have h2 := key Sw _ hSw0 hden
  have hdiv : ∀ a b T : ℝ, T ≠ 0 → (a / T) / (b / T) = a / b := by
    intro a b T hT
    rcases eq_or_ne b 0 with hb | hb
    · simp [hb]
    · field_simp
  have hfinal := h1.div h2 (ne_of_gt hw)
  rw [mul_comm Sw Sα, mul_div_assoc, div_self (ne_of_gt hw), mul_one] at hfinal
  refine hfinal.congr' ?_
  filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
  exact hdiv _ _ T hT

/-! ### 4. The return kernel of a finite set of primes -/

/-- The **return kernel** of a finite set of primes: `Π_{p ∈ P} (2 + 2 cos(τ log p))`.  It is
nonnegative, has mean `2^{|P|}` and is maximal exactly at the heights where every `p ∈ P` returns
to phase one, that is on the return set of the Euler head carried by `P`. -/
def primeReturnKernel (P : Finset ℕ) (τ : ℝ) : ℝ :=
  ∏ p ∈ P, (2 + 2 * Real.cos (τ * Real.log p))

/-- The squarefree products of a finite set of primes. -/
def squarefreeProducts (P : Finset ℕ) : Finset ℕ :=
  P.powerset.image (fun t => ∏ p ∈ t, p)

theorem injOn_prod_powerset {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) ↑P.powerset := by
  intro t ht t' ht' h
  have hsub : ∀ u : Finset ℕ, u ∈ P.powerset → (∏ p ∈ u, p).primeFactors = u := fun u hu =>
    Nat.primeFactors_prod fun p hp => hP p (Finset.mem_powerset.mp hu hp)
  have h1 := hsub t (by simpa using ht)
  have h2 := hsub t' (by simpa using ht')
  rw [← h1, ← h2]
  exact congrArg Nat.primeFactors h

/-- The return-kernel probe: the sum of the squarefree products of `P` is the Euler head
`Π_{p ∈ P}(1 + p^{iτ})`. -/
theorem integerHeightPoly_squarefreeProducts {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (τ : ℝ) :
    integerHeightPoly (squarefreeProducts P) (fun _ => 1) τ
      = ∏ p ∈ P, (Complex.exp (((τ * Real.log p : ℝ) : ℂ) * Complex.I) + 1) := by
  have hterm : ∀ t ∈ P.powerset,
      Complex.exp (((τ * Real.log ((∏ p ∈ t, p : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)
        = ∏ p ∈ t, Complex.exp (((τ * Real.log p : ℝ) : ℂ) * Complex.I) := by
    intro t ht
    have hne : ∀ p ∈ t, ((p : ℝ)) ≠ 0 := by
      intro p hp
      exact Nat.cast_ne_zero.mpr (hP p (Finset.mem_powerset.mp ht hp)).pos.ne'
    have hlog : Real.log ((∏ p ∈ t, p : ℕ) : ℝ) = ∑ p ∈ t, Real.log p := by
      rw [Nat.cast_prod]
      exact Real.log_prod hne
    have hcast : ((τ * ∑ p ∈ t, Real.log p : ℝ) : ℂ) * Complex.I
        = ∑ p ∈ t, ((τ * Real.log p : ℝ) : ℂ) * Complex.I := by
      rw [Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun p _ => by rw [Complex.ofReal_mul]
    rw [hlog, hcast, Complex.exp_sum]
  rw [integerHeightPoly, familyHeightPoly, squarefreeProducts,
    Finset.sum_image (injOn_prod_powerset hP)]
  simp only [id_eq, one_mul]
  rw [Finset.prod_add]
  simp only [Finset.prod_const_one, mul_one]
  exact Finset.sum_congr rfl hterm

/-- `|1 + e^{iθ}|² = 2 + 2 cos θ`. -/
private theorem normSq_exp_add_one (θ : ℝ) :
    ‖Complex.exp ((θ : ℂ) * Complex.I) + 1‖ ^ 2 = 2 + 2 * Real.cos θ := by
  rw [show Complex.exp ((θ : ℂ) * Complex.I) + 1
      = 1 + Complex.exp ((θ : ℂ) * Complex.I) from add_comm _ _,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.one_re, Complex.one_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  nlinarith [Real.sin_sq_add_cos_sq θ]

/-- The square modulus of the return-kernel probe is the return kernel. -/
theorem normSq_integerHeightPoly_squarefreeProducts {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    (τ : ℝ) :
    ‖integerHeightPoly (squarefreeProducts P) (fun _ => 1) τ‖ ^ 2 = primeReturnKernel P τ := by
  rw [integerHeightPoly_squarefreeProducts hP, primeReturnKernel, norm_prod, ← Finset.prod_pow]
  exact Finset.prod_congr rfl fun p _ => normSq_exp_add_one (τ * Real.log p)

/-- Squarefree products of primes below `y` are `y`-smooth. -/
theorem squarefreeProducts_subset_smoothNumbers {y : ℕ} {P : Finset ℕ}
    (hP : ∀ p ∈ P, p ∈ Nat.primesBelow y) :
    ∀ s ∈ squarefreeProducts P, s ∈ Nat.smoothNumbers y := by
  intro s hs
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  have hprime : ∀ p ∈ t, p.Prime := fun p hp =>
    Nat.prime_of_mem_primesBelow (hP p (Finset.mem_powerset.mp ht hp))
  refine Nat.mem_smoothNumbers_iff_primeFactors_subset.mpr ⟨?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun p hp => (hprime p hp).pos.ne'
  · rw [Nat.primeFactors_prod hprime]
    exact fun p hp => hP p (Finset.mem_powerset.mp ht hp)

/-- Every squarefree product of `P` divides, hence is at most, the radical `Π_{p ∈ P} p`. -/
theorem le_prod_of_mem_squarefreeProducts {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime)
    {s : ℕ} (hs : s ∈ squarefreeProducts P) : s ≤ ∏ p ∈ P, p := by
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hs
  have hpos : 0 < ∏ p ∈ P, p :=
    Finset.prod_pos fun p hp => (hP p hp).pos
  exact Nat.le_of_dvd hpos (Finset.prod_dvd_prod_of_subset _ _ _ (Finset.mem_powerset.mp ht))

/-- The number of squarefree products is `2^{|P|}`, so the return kernel has positive mean. -/
theorem sum_normSq_one_squarefreeProducts {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) :
    ∑ _s ∈ squarefreeProducts P, ‖(1 : ℂ)‖ ^ 2 = 2 ^ P.card := by
  rw [Finset.sum_const, squarefreeProducts, Finset.card_image_of_injOn (injOn_prod_powerset hP),
    Finset.card_powerset]
  simp

/-- **The return set of a finite Euler head does not inflate the rough mean square.** For every
finite set `P` of primes below `y` and every Dirichlet polynomial `D` carried by `y`-rough
integers, the mean square of `D` weighted by the return kernel of `P` converges to the unweighted
mean square `Σ_m |α_m|²`.  Conditioning the heights on the return of the primes below `y` — to any
prescribed phase, with any concentration — is free. -/
theorem tendsto_primeReturnKernel_weighted_roughMeanSquare {y : ℕ} {P M : Finset ℕ} {α : ℕ → ℂ}
    (hP : ∀ p ∈ P, p ∈ Nat.primesBelow y)
    (hM0 : ∀ m ∈ M, m ≠ 0) (hMr : ∀ m ∈ M, ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m) :
    Tendsto (fun T : ℝ =>
        (∫ τ in (0 : ℝ)..T, primeReturnKernel P τ * ‖integerHeightPoly M α τ‖ ^ 2) /
          (∫ τ in (0 : ℝ)..T, primeReturnKernel P τ))
      atTop (𝓝 (∑ m ∈ M, ‖α m‖ ^ 2)) := by
  classical
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow (hP p hp)
  set Q : ℕ := ∏ p ∈ P, p with hQ
  set Mmax : ℕ := M.sup id with hMmax
  have hbase := tendsto_headWeighted_roughMeanSquare (y := y) (S := squarefreeProducts P) (M := M)
    (w := fun _ => 1) (α := α) (N := Q * (Mmax + 1))
    (squarefreeProducts_subset_smoothNumbers hP) hM0 hMr
    (fun s hs => le_trans (le_prod_of_mem_squarefreeProducts hprime hs)
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
    (fun s hs m hm => Nat.mul_le_mul (le_prod_of_mem_squarefreeProducts hprime hs)
      (le_trans (Finset.le_sup (f := id) hm) (Nat.le_succ _)))
    (by
      rw [sum_normSq_one_squarefreeProducts hprime]
      positivity)
  simpa only [normSq_integerHeightPoly_squarefreeProducts hprime] using hbase

/-! ### 5. Most of the return kernel's mass sits at typical heights -/

theorem primeReturnKernel_nonneg (P : Finset ℕ) (τ : ℝ) : 0 ≤ primeReturnKernel P τ :=
  Finset.prod_nonneg fun p _ => by
    have := Real.neg_one_le_cos (τ * Real.log p)
    linarith

theorem continuous_integerHeightPoly (A : Finset ℕ) (f : ℕ → ℂ) :
    Continuous (integerHeightPoly A f) := by
  unfold integerHeightPoly familyHeightPoly
  refine continuous_finsetSum _ fun n _ => continuous_const.mul ?_
  exact Complex.continuous_exp.comp
    ((Complex.continuous_ofReal.comp (continuous_id.mul continuous_const)).mul continuous_const)

theorem continuous_primeReturnKernel (P : Finset ℕ) : Continuous (primeReturnKernel P) := by
  unfold primeReturnKernel
  refine continuous_finsetProd _ fun p _ => continuous_const.add (continuous_const.mul ?_)
  exact Real.continuous_cos.comp (continuous_id.mul continuous_const)

/-- Chebyshev against a nonnegative weight: the weight's mass on `{c ≤ D}` is at most `1/c` times
the weighted integral of `D`. -/
theorem mul_setIntegral_le_intervalIntegral_mul {K D : ℝ → ℝ} (hK : Continuous K)
    (hKnn : ∀ τ, 0 ≤ K τ) (hD : Continuous D) (hDnn : ∀ τ, 0 ≤ D τ) (c : ℝ) {T : ℝ}
    (hT : 0 ≤ T) :
    c * (∫ τ in {σ : ℝ | c ≤ D σ} ∩ Set.Ioc 0 T, K τ) ≤ ∫ τ in (0 : ℝ)..T, K τ * D τ := by
  have hmeas : MeasurableSet ({σ : ℝ | c ≤ D σ} ∩ Set.Ioc 0 T) :=
    (isClosed_le continuous_const hD).measurableSet.inter measurableSet_Ioc
  have hsub : {σ : ℝ | c ≤ D σ} ∩ Set.Ioc 0 T ⊆ Set.Ioc 0 T := Set.inter_subset_right
  have hKD : Continuous fun τ => K τ * D τ := hK.mul hD
  have hIocKD : MeasureTheory.IntegrableOn (fun τ => K τ * D τ) (Set.Ioc 0 T) :=
    hKD.integrableOn_Ioc
  have hsKD : MeasureTheory.IntegrableOn (fun τ => K τ * D τ)
      ({σ : ℝ | c ≤ D σ} ∩ Set.Ioc 0 T) := hIocKD.mono_set hsub
  have hscK : MeasureTheory.IntegrableOn (fun τ => c * K τ)
      ({σ : ℝ | c ≤ D σ} ∩ Set.Ioc 0 T) :=
    ((continuous_const.mul hK).integrableOn_Ioc (a := (0 : ℝ)) (b := T)).mono_set hsub
  calc c * (∫ τ in {σ : ℝ | c ≤ D σ} ∩ Set.Ioc 0 T, K τ)
      = ∫ τ in {σ : ℝ | c ≤ D σ} ∩ Set.Ioc 0 T, c * K τ :=
        (MeasureTheory.integral_const_mul c K).symm
    _ ≤ ∫ τ in {σ : ℝ | c ≤ D σ} ∩ Set.Ioc 0 T, K τ * D τ := by
        refine MeasureTheory.setIntegral_mono_on hscK hsKD hmeas fun τ hτ => ?_
        have hc : c ≤ D τ := hτ.1
        have := hKnn τ
        nlinarith
    _ ≤ ∫ τ in Set.Ioc 0 T, K τ * D τ := by
        refine MeasureTheory.setIntegral_mono_set hIocKD ?_ (Filter.Eventually.of_forall hsub)
        filter_upwards with τ using mul_nonneg (hKnn τ) (hDnn τ)
    _ = ∫ τ in (0 : ℝ)..T, K τ * D τ := (intervalIntegral.integral_of_le hT).symm

/-- The cutoff used by the return-kernel bracket: the radical of `P` times one more than the
largest rough index. -/
def returnKernelCutoff (P M : Finset ℕ) : ℕ := (∏ p ∈ P, p) * (M.sup id + 1)

/-- **The return-kernel bracket.** The return kernel of `P` weights the rough mean square to
`T · 2^{|P|} Σ_m |α_m|²` up to one horizon-free error. -/
theorem norm_integral_primeReturnKernel_mul_rough_sub_diag_le {y : ℕ} {P M : Finset ℕ} {α : ℕ → ℂ}
    (hP : ∀ p ∈ P, p ∈ Nat.primesBelow y)
    (hM0 : ∀ m ∈ M, m ≠ 0) (hMr : ∀ m ∈ M, ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m) (T : ℝ) :
    |(∫ τ in (0 : ℝ)..T, primeReturnKernel P τ * ‖integerHeightPoly M α τ‖ ^ 2)
        - T * ((2 : ℝ) ^ P.card * ∑ m ∈ M, ‖α m‖ ^ 2)|
      ≤ 4 * (returnKernelCutoff P M : ℝ) * (1 + Real.log (returnKernelCutoff P M)) *
          ((2 : ℝ) ^ P.card * ∑ m ∈ M, ‖α m‖ ^ 2) := by
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow (hP p hp)
  have hbase := norm_integral_normSq_smooth_mul_rough_sub_diag_le (y := y)
    (S := squarefreeProducts P) (M := M) (w := fun _ => 1) (α := α)
    (N := returnKernelCutoff P M) T (squarefreeProducts_subset_smoothNumbers hP) hM0 hMr
    (fun s hs m hm => Nat.mul_le_mul (le_prod_of_mem_squarefreeProducts hprime hs)
      (le_trans (Finset.le_sup (f := id) hm) (Nat.le_succ _)))
  rw [sum_normSq_one_squarefreeProducts hprime] at hbase
  simpa only [normSq_integerHeightPoly_squarefreeProducts hprime, Nat.cast_pow,
    Nat.cast_ofNat] using hbase

/-- **The return set of a finite Euler head is not an exceptional set for a rough polynomial.**
At most the fraction `1/λ` of the return kernel's mass, up to the horizon-free error, sits at
heights where the rough polynomial exceeds `λ` times its mean square.  So an estimate for a rough
Dirichlet polynomial averaged over *all* heights does control it on the return set of the primes
below `y`. -/
theorem mul_setIntegral_primeReturnKernel_badHeights_le {y : ℕ} {P M : Finset ℕ} {α : ℕ → ℂ}
    (hP : ∀ p ∈ P, p ∈ Nat.primesBelow y)
    (hM0 : ∀ m ∈ M, m ≠ 0) (hMr : ∀ m ∈ M, ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m)
    (hα : 0 < ∑ m ∈ M, ‖α m‖ ^ 2) (lam : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    lam * (∫ τ in {σ : ℝ | lam * (∑ m ∈ M, ‖α m‖ ^ 2) ≤ ‖integerHeightPoly M α σ‖ ^ 2} ∩
        Set.Ioc 0 T, primeReturnKernel P τ)
      ≤ (T + 4 * (returnKernelCutoff P M : ℝ) * (1 + Real.log (returnKernelCutoff P M)))
          * (2 : ℝ) ^ P.card := by
  set Sα : ℝ := ∑ m ∈ M, ‖α m‖ ^ 2 with hSα
  set C : ℝ := 4 * (returnKernelCutoff P M : ℝ) * (1 + Real.log (returnKernelCutoff P M)) with hC
  have hcheb := mul_setIntegral_le_intervalIntegral_mul (K := primeReturnKernel P)
    (D := fun τ => ‖integerHeightPoly M α τ‖ ^ 2) (continuous_primeReturnKernel P)
    (primeReturnKernel_nonneg P)
    ((continuous_integerHeightPoly M α).norm.pow 2) (fun τ => by positivity) (lam * Sα) hT
  have hbr := norm_integral_primeReturnKernel_mul_rough_sub_diag_le (y := y) (α := α) hP hM0 hMr T
  have hup : (∫ τ in (0 : ℝ)..T, primeReturnKernel P τ * ‖integerHeightPoly M α τ‖ ^ 2)
      ≤ (T + C) * ((2 : ℝ) ^ P.card * Sα) := by
    have := abs_le.mp hbr
    nlinarith [this.2]
  have hmass : lam * Sα *
      (∫ τ in {σ : ℝ | lam * Sα ≤ ‖integerHeightPoly M α σ‖ ^ 2} ∩ Set.Ioc 0 T,
        primeReturnKernel P τ) ≤ (T + C) * ((2 : ℝ) ^ P.card * Sα) :=
    le_trans hcheb hup
  have hfin : lam * (∫ τ in {σ : ℝ | lam * Sα ≤ ‖integerHeightPoly M α σ‖ ^ 2} ∩ Set.Ioc 0 T,
        primeReturnKernel P τ) * Sα ≤ (T + C) * (2 : ℝ) ^ P.card * Sα := by
    calc lam * (∫ τ in {σ : ℝ | lam * Sα ≤ ‖integerHeightPoly M α σ‖ ^ 2} ∩ Set.Ioc 0 T,
          primeReturnKernel P τ) * Sα
        = lam * Sα * (∫ τ in {σ : ℝ | lam * Sα ≤ ‖integerHeightPoly M α σ‖ ^ 2} ∩ Set.Ioc 0 T,
            primeReturnKernel P τ) := by ring
      _ ≤ (T + C) * ((2 : ℝ) ^ P.card * Sα) := hmass
      _ = (T + C) * (2 : ℝ) ^ P.card * Sα := by ring
  exact le_of_mul_le_mul_right hfin hα

/-! ### 6. Return and smallness at once, uniformly in the cutoff -/

/-- The return kernel's own mass bracket, at the cutoff of the decoupling bracket. -/
theorem abs_integral_primeReturnKernel_sub_diag_le {y : ℕ} {P : Finset ℕ} (M : Finset ℕ)
    (hP : ∀ p ∈ P, p ∈ Nat.primesBelow y) (T : ℝ) :
    |(∫ τ in (0 : ℝ)..T, primeReturnKernel P τ) - T * (2 : ℝ) ^ P.card|
      ≤ 4 * (returnKernelCutoff P M : ℝ) * (1 + Real.log (returnKernelCutoff P M)) *
          (2 : ℝ) ^ P.card := by
  have hprime : ∀ p ∈ P, p.Prime := fun p hp => Nat.prime_of_mem_primesBelow (hP p hp)
  have hbase := norm_integral_normSq_head_sub_diag_le (y := y) (S := squarefreeProducts P)
    (w := fun _ => 1) (N := returnKernelCutoff P M) T
    (squarefreeProducts_subset_smoothNumbers hP)
    (fun s hs => le_trans (le_prod_of_mem_squarefreeProducts hprime hs)
      (Nat.le_mul_of_pos_right _ (Nat.succ_pos _)))
  rw [sum_normSq_one_squarefreeProducts hprime] at hbase
  simpa only [normSq_integerHeightPoly_squarefreeProducts hprime, Nat.cast_pow,
    Nat.cast_ofNat] using hbase

/-- **Return and smallness at once, with no relation between the cutoff and the budget.** For every
finite set `P` of primes below `y`, every `y`-rough Dirichlet polynomial and every `λ > 1`, the
heights at which the rough polynomial stays below `λ` times its mean square carry a positive share
of the return kernel's mass once the horizon exceeds the explicit cutoff error.

This is what a bound on the rough polynomial averaged over *all* heights cannot give by itself: a
pigeonhole between a bad-set density `δ` and the return density `η(y)` needs `δ < η(y)`, and the
return density decays in the cutoff `y` while the bad-set bound improves only as `y` grows.  Here
the bad set is small **relative to the kernel**, at every cutoff. -/
theorem le_setIntegral_primeReturnKernel_goodHeights {y : ℕ} {P M : Finset ℕ} {α : ℕ → ℂ}
    (hP : ∀ p ∈ P, p ∈ Nat.primesBelow y)
    (hM0 : ∀ m ∈ M, m ≠ 0) (hMr : ∀ m ∈ M, ∀ p ∈ Nat.primesBelow y, ¬ p ∣ m)
    (hα : 0 < ∑ m ∈ M, ‖α m‖ ^ 2) {lam T : ℝ} (hlam : 0 < lam) (hT : 0 ≤ T) :
    (T - 4 * (returnKernelCutoff P M : ℝ) * (1 + Real.log (returnKernelCutoff P M))) *
          (2 : ℝ) ^ P.card
        - (T + 4 * (returnKernelCutoff P M : ℝ) * (1 + Real.log (returnKernelCutoff P M))) *
            (2 : ℝ) ^ P.card / lam
      ≤ ∫ τ in {σ : ℝ | ‖integerHeightPoly M α σ‖ ^ 2 < lam * (∑ m ∈ M, ‖α m‖ ^ 2)} ∩
          Set.Ioc 0 T, primeReturnKernel P τ := by
  classical
  set Sα : ℝ := ∑ m ∈ M, ‖α m‖ ^ 2 with hSα
  set C : ℝ := 4 * (returnKernelCutoff P M : ℝ) * (1 + Real.log (returnKernelCutoff P M)) with hC
  set bad : Set ℝ := {σ : ℝ | lam * Sα ≤ ‖integerHeightPoly M α σ‖ ^ 2} with hbad
  set good : Set ℝ := {σ : ℝ | ‖integerHeightPoly M α σ‖ ^ 2 < lam * Sα} with hgood
  have hKc : Continuous (primeReturnKernel P) := continuous_primeReturnKernel P
  have hDc : Continuous fun σ : ℝ => ‖integerHeightPoly M α σ‖ ^ 2 :=
    (continuous_integerHeightPoly M α).norm.pow 2
  have hbadmeas : MeasurableSet bad := (isClosed_le continuous_const hDc).measurableSet
  -- the kernel's mass splits over the good and bad parts
  have hdisj : Disjoint (good ∩ Set.Ioc 0 T) (bad ∩ Set.Ioc 0 T) := by
    refine Set.disjoint_left.mpr fun σ hσg hσb => ?_
    have h1 := hσg.1
    have h2 := hσb.1
    simp only [hgood, hbad, Set.mem_setOf_eq] at h1 h2
    linarith
  have hunion : good ∩ Set.Ioc 0 T ∪ bad ∩ Set.Ioc 0 T = Set.Ioc 0 T := by
    ext σ
    simp only [hgood, hbad, Set.mem_union, Set.mem_inter_iff, Set.mem_setOf_eq]
    constructor
    · rintro (⟨_, h⟩ | ⟨_, h⟩) <;> exact h
    · intro h
      rcases lt_or_ge (‖integerHeightPoly M α σ‖ ^ 2) (lam * Sα) with hc | hc
      · exact Or.inl ⟨hc, h⟩
      · exact Or.inr ⟨hc, h⟩
  have hint : MeasureTheory.IntegrableOn (primeReturnKernel P) (Set.Ioc 0 T) :=
    hKc.integrableOn_Ioc
  have hsplit : (∫ τ in Set.Ioc 0 T, primeReturnKernel P τ)
      = (∫ τ in good ∩ Set.Ioc 0 T, primeReturnKernel P τ) +
        ∫ τ in bad ∩ Set.Ioc 0 T, primeReturnKernel P τ := by
    conv_lhs => rw [← hunion]
    exact MeasureTheory.setIntegral_union hdisj (hbadmeas.inter measurableSet_Ioc)
      (hint.mono_set Set.inter_subset_right) (hint.mono_set Set.inter_subset_right)
  -- the bad part is at most `1/λ` of the kernel's total allowance
  have hbadle := mul_setIntegral_primeReturnKernel_badHeights_le hP hM0 hMr hα lam hT
  have hbadbound : (∫ τ in bad ∩ Set.Ioc 0 T, primeReturnKernel P τ) ≤ (T + C) * (2 : ℝ) ^ P.card / lam := by
    rw [le_div_iff₀ hlam, mul_comm]
    exact hbadle
  -- the kernel's own mass is at least `(T − C) 2^{|P|}`
  have hmass := abs_le.mp (abs_integral_primeReturnKernel_sub_diag_le (y := y) M hP T)
  have hIoc : (∫ τ in Set.Ioc 0 T, primeReturnKernel P τ)
      = ∫ τ in (0 : ℝ)..T, primeReturnKernel P τ := (intervalIntegral.integral_of_le hT).symm
  rw [hIoc] at hsplit
  have hlow : (T - C) * (2 : ℝ) ^ P.card ≤ ∫ τ in (0 : ℝ)..T, primeReturnKernel P τ := by
    nlinarith [hmass.1]
  linarith [hsplit, hbadbound, hlow]

end

end RHTower
