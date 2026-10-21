import GaloisForLFunctions.RHTower.ExponentialTuplesAndAnalyticMembershipInPrimeSpan

/-!
# The closed span of the prime tuples is the closure of the polynomial tuples

On finitely many discs `|s − z i| < ρ i` with `Re (z i) + ρ i ≤ b < 1`, three closed subspaces of
the direct sum `DiscTuple ι` coincide:

* `primeSpan`, the closed span of the prime tuples `(q ↦ p^{−(z i + ρ i q)})_i`;
* `expTupleSpan`, the closed span of the exponential tuples `(q ↦ e^{−(z i + ρ i q)ξ})_i`, `ξ ∈ ℝ`;
* `polyTupleSpan c₀`, the closed span of the monomial tuples `(q ↦ (z i + ρ i q − c₀)^k)_i`, for
  any centre `c₀`.

The prime tuples are the exponential tuples at `ξ = log p`; every exponential tuple lies in
`primeSpan` because the pairing function `F_e` of a tuple orthogonal to the prime tuples vanishes
identically; the monomial tuples are limits of finite differences of exponential tuples; and the
prime tuples are tuples of the entire functions `s ↦ p^{−s}`, hence limits of their Taylor
polynomials.  The orthogonal complement of all three is the space of tuples `e` with `F_e ≡ 0`.

So the tuples admissible for the joint Pechersky approximation are exactly the limits of the
"diagonal" restrictions of polynomials, equivalently of entire functions, to the discs.
-/

open Complex Filter Topology Finset Metric
open GaloisForLFunctions.HTGeometry
open scoped InnerProductSpace ComplexConjugate

noncomputable section

namespace RHTower

variable {ι : Type*} [Fintype ι]

/-- The closed span of the monomial tuples centred at `c₀`. -/
def polyTupleSpan (z : ι → ℂ) (ρ : ι → ℝ) (c₀ : ℂ) : Submodule ℂ (DiscTuple ι) :=
  (Submodule.span ℂ (Set.range (monoTuple z ρ c₀))).topologicalClosure

/-- The closed span of the exponential tuples. -/
def expTupleSpan (z : ι → ℂ) (ρ : ι → ℝ) : Submodule ℂ (DiscTuple ι) :=
  (Submodule.span ℂ (Set.range (expTuple z ρ))).topologicalClosure

theorem monoTuple_mem_polyTupleSpan (z : ι → ℂ) (ρ : ι → ℝ) (c₀ : ℂ) (k : ℕ) :
    monoTuple z ρ c₀ k ∈ polyTupleSpan z ρ c₀ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨k, rfl⟩)

theorem expTuple_mem_expTupleSpan (z : ι → ℂ) (ρ : ι → ℝ) (ξ : ℝ) :
    expTuple z ρ ξ ∈ expTupleSpan z ρ :=
  Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨ξ, rfl⟩)

/-! ## Prime vectors are exponential vectors -/

/-- The prime vector at `p` is the exponential vector at `ξ = log p`. -/
theorem primeVector_eq_expVector (z₀ : ℂ) {ρ : ℝ} (hρ : 0 ≤ ρ) {p : ℕ} (hp : 0 < p) :
    primeVector z₀ hρ hp = expVector z₀ ρ (Real.log p) := by
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  have hlog : Complex.log (p : ℂ) = ((Real.log p : ℝ) : ℂ) := by
    rw [Complex.ofReal_log (Nat.cast_nonneg p), Complex.ofReal_natCast]
  refine lp.ext (funext fun k => ?_)
  show primeVectorCoeff z₀ ρ p k = expVectorCoeff z₀ ρ (Real.log p) k
  rw [primeVectorCoeff, expVectorCoeff, Complex.cpow_def_of_ne_zero hp0, hlog]
  congr 2
  ring

/-- The prime tuple at a prime `n` is the exponential tuple at `ξ = log n`. -/
theorem primeTuple_eq_expTuple (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) {n : ℕ}
    (hn : n.Prime) : primeTuple z hρ n = expTuple z ρ (Real.log n) := by
  refine PiLp.ext fun i => ?_
  rw [primeTuple_apply, expTuple_apply, primeTerm_of_prime _ _ hn, primeVector_eq_expVector]

/-! ## The three closed spans coincide -/

theorem primeTuple_mem_expTupleSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (n : ℕ) :
    primeTuple z hρ n ∈ expTupleSpan z ρ := by
  by_cases hn : n.Prime
  · rw [primeTuple_eq_expTuple z hρ hn]
    exact expTuple_mem_expTupleSpan z ρ _
  · rw [primeTuple_of_not_prime z hρ hn]
    exact Submodule.zero_mem _

/-- The prime tuple at `n` is the tuple of the entire function `s ↦ n^{−s}`, hence lies in the
closure of the polynomial tuples about any centre. -/
theorem primeTuple_mem_polyTupleSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (c₀ : ℂ)
    (n : ℕ) : primeTuple z hρ n ∈ polyTupleSpan z ρ c₀ := by
  by_cases hn : n.Prime
  · have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne_zero
    refine mem_of_differentiableOn_ball_of_monoTuple_mem z hρ
      (Submodule.isClosed_topologicalClosure _) (monoTuple_mem_polyTupleSpan z ρ c₀)
      (by norm_num : (1 : ℝ) < 2) (R₀ := ∑ j, (‖z j - c₀‖ + ρ j * 2) + 1) (fun i => ?_)
      (F := fun s : ℂ => (n : ℂ) ^ (-s))
      (differentiable_id.neg.const_cpow (Or.inl hn0)).differentiableOn fun i q hq => ?_
    · have := Finset.single_le_sum (f := fun j => ‖z j - c₀‖ + ρ j * 2)
        (fun j _ => by have := hρ j; positivity) (mem_univ i)
      linarith
    · rw [primeTuple_apply, hardyFun_primeTerm _ _ n hq, if_pos hn]
  · rw [primeTuple_of_not_prime z hρ hn]
    exact Submodule.zero_mem _

theorem primeSpan_le_expTupleSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) :
    primeSpan z hρ ≤ expTupleSpan z ρ := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  exact primeTuple_mem_expTupleSpan z hρ n

theorem primeSpan_le_polyTupleSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i) (c₀ : ℂ) :
    primeSpan z hρ ≤ polyTupleSpan z ρ c₀ := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨n, rfl⟩
  exact primeTuple_mem_polyTupleSpan z hρ c₀ n

theorem expTupleSpan_le_primeSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) :
    expTupleSpan z ρ ≤ primeSpan z hρ := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨ξ, rfl⟩
  exact expTuple_mem_primeSpan z hρ hb hb1 ξ

theorem polyTupleSpan_le_primeSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) (c₀ : ℂ) :
    polyTupleSpan z ρ c₀ ≤ primeSpan z hρ := by
  refine Submodule.topologicalClosure_minimal _ ?_ (Submodule.isClosed_topologicalClosure _)
  rw [Submodule.span_le]
  rintro _ ⟨k, rfl⟩
  exact monoTuple_mem_primeSpan z hρ hb hb1 c₀ k

/-- **The closed span of the prime tuples is the closed span of the exponential tuples.** -/
theorem primeSpan_eq_expTupleSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) :
    primeSpan z hρ = expTupleSpan z ρ :=
  le_antisymm (primeSpan_le_expTupleSpan z hρ) (expTupleSpan_le_primeSpan z hρ hb hb1)

/-- **The closed span of the prime tuples is the closure of the polynomial tuples**, about any
centre. -/
theorem primeSpan_eq_polyTupleSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) (c₀ : ℂ) :
    primeSpan z hρ = polyTupleSpan z ρ c₀ :=
  le_antisymm (primeSpan_le_polyTupleSpan z hρ c₀) (polyTupleSpan_le_primeSpan z hρ hb hb1 c₀)

/-- The polynomial closure does not depend on the centre. -/
theorem polyTupleSpan_eq_polyTupleSpan (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) (c₀ c₁ : ℂ) :
    polyTupleSpan z ρ c₀ = polyTupleSpan z ρ c₁ := by
  rw [← primeSpan_eq_polyTupleSpan z hρ hb hb1 c₀, ← primeSpan_eq_polyTupleSpan z hρ hb hb1 c₁]

/-! ## The orthogonal complement -/

/-- **The orthogonal complement of the closed span is the kernel of the pairing**: `e ⊥ primeSpan`
iff `F_e ≡ 0`. -/
theorem mem_orthogonal_primeSpan_iff_tuplePairing_eq_zero (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) (e : DiscTuple ι) :
    e ∈ (primeSpan z hρ)ᗮ ↔ tuplePairing z ρ e = 0 :=
  ⟨tuplePairing_eq_zero_of_mem_orthogonal z hρ hb hb1,
    mem_orthogonal_primeSpan_of_tuplePairing_eq_zero z hρ⟩

/-- A tuple lies in the closed span iff it is orthogonal to every tuple with vanishing pairing
function. -/
theorem mem_primeSpan_iff_forall_tuplePairing_eq_zero (z : ι → ℂ) {ρ : ι → ℝ}
    (hρ : ∀ i, 0 ≤ ρ i) {b : ℝ} (hb : ∀ i, (z i).re + ρ i ≤ b) (hb1 : b < 1) (t : DiscTuple ι) :
    t ∈ primeSpan z hρ ↔ ∀ e : DiscTuple ι, tuplePairing z ρ e = 0 → ⟪e, t⟫_ℂ = 0 := by
  rw [← Submodule.orthogonal_orthogonal (primeSpan z hρ), Submodule.mem_orthogonal]
  constructor
  · intro h e he
    exact h e ((mem_orthogonal_primeSpan_iff_tuplePairing_eq_zero z hρ hb hb1 e).mpr he)
  · intro h e he
    exact h e ((mem_orthogonal_primeSpan_iff_tuplePairing_eq_zero z hρ hb hb1 e).mp he)

/-- **The single-disc case: the prime vectors are complete in the Hardy space.**  For one disc the
closed span is everything, since a nonzero `e` has `Φ_e ≢ 0`. -/
theorem primeSpan_eq_top_of_unique [Unique ι] (z : ι → ℂ) {ρ : ι → ℝ} (hρ : ∀ i, 0 ≤ ρ i)
    (hρpos : ∀ i, 0 < ρ i) (hσ : ∀ i, 1 / 2 ≤ (z i).re) (hρσ : ∀ i, ρ i < 1 - (z i).re)
    (hρ5 : ∀ i, ρ i < 5 / 12) : primeSpan z hρ = ⊤ := by
  rw [eq_top_iff]
  intro t _
  rw [← Submodule.orthogonal_orthogonal (primeSpan z hρ), Submodule.mem_orthogonal]
  intro e he
  have hF := tuplePairing_eq_zero_of_mem_orthogonal z hρ (b := (z default).re + ρ default)
    (fun i => by rw [Unique.eq_default i]) (by linarith [hρσ default]) he
  -- `F_e = e^{−conj(z) ξ} Φ_{e default}(ξ)`, so `Φ_{e default} ≡ 0`, so `e default = 0`
  have hΦ : coefficientTransform (ρ default) (e default) = 0 := by
    funext ξ
    have h := congrFun hF ξ
    simp only [tuplePairing, Fintype.sum_unique, Pi.zero_apply] at h
    rcases mul_eq_zero.mp h with h0 | h0
    · exact absurd h0 (Complex.exp_ne_zero _)
    · exact h0
  have he0 : e default = 0 := by
    by_contra hne
    obtain ⟨N, hN⟩ := exists_sum_norm_inner_primeTerm_gt (z default) (hρpos default) (hσ default)
      (hρσ default) (hρ5 default) hne 0
    have : ∀ n, ⟪primeTerm (z default) (hρ default) n, e default⟫_ℂ = 0 := by
      intro n
      by_cases hn : n.Prime
      · rw [primeTerm_of_prime _ _ hn, inner_primeVector, hΦ]
        simp
      · rw [primeTerm_of_not_prime _ _ hn, inner_zero_left]
    simp only [this, norm_zero, sum_const_zero, lt_self_iff_false] at hN
  have : e = 0 := PiLp.ext fun i => by rw [Unique.eq_default i, he0]; rfl
  rw [this, inner_zero_left]

end RHTower
