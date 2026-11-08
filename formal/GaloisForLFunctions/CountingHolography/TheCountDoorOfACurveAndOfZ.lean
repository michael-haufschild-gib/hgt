import GaloisForLFunctions.CountingHolography.TheTateLimitOfACount
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FrobeniusSpanHodgeIndexIsRH
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHyperellipticCalibration

/-!
# The count door of a curve and of `ℤ`

**The Tate principle in both directions** (`exists_count_tateLimit_iff`). A function `Q` on an
additive monoid, homogeneous of degree two along rays, is the quadratic growth `K(m x)/m² → Q x` of
an `ℕ`-valued count `K` iff `Q ≥ 0`.

**Curves** (`curve_countDoor`). For a curve datum, the Castelnuovo–Severi defect of integral span
classes `D = Σ d_k Γ_k`, `d_k ∈ ℤ`, is the Tate limit of a count iff the datum is unitary: Hodge index
on integral classes already forces RH (`unitary_of_intSpanDefect_nonneg`, by rational scaling and
continuity).

**On a true curve the form is a count** (`hyperelliptic_spanDefect_is_count`). For `y² = f(x)` the
defect of an integral class is an integer polynomial in `q` and the point counts
`N_j = #C(𝔽_{q^j})`, and it is a natural number: the count is the intersection number itself,
exactly homogeneous, `K(m D) = m² K(D)`.

**Over `ℤ`** the same door is `riemannHypothesis_iff_tateLimit_of_count`, with `Q` the Krein square
of the integer probes, a real Toeplitz form in `log(m/n)`. The skeleton is complete except the
count: on curves the count is given by point counts before any sign is known, over `ℤ` nothing
plays that role.
-/

open Filter Topology Finset

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open ArithmeticCastelnuovoSeveri

/-! ### The Tate principle -/

/-- **The Tate principle in both directions.** -/
theorem exists_count_tateLimit_iff {M : Type*} [AddCommMonoid M] (Q : M → ℝ)
    (hQ : ∀ (m : ℕ) (x : M), Q (m • x) = (m : ℝ) ^ 2 * Q x) :
    (∃ K : M → ℕ, ∀ x, Tendsto (fun m : ℕ => (K (m • x) : ℝ) / (m : ℝ) ^ 2) atTop (𝓝 (Q x))) ↔
      ∀ x, 0 ≤ Q x := by
  constructor
  · rintro ⟨K, hK⟩ x
    exact nonneg_of_tateLimit (K := fun y => (K y : ℝ)) (fun _ => Nat.cast_nonneg _) (hK x)
  · intro h
    refine ⟨fun x => ⌊Q x⌋₊, fun x => ?_⟩
    simp only [hQ]
    exact tendsto_floor_div_sq (h x)

/-! ### Curves: Hodge index on integral classes -/

namespace CurveDatum'

variable {ι : Type*} [Fintype ι] (D : CurveDatum ι)

/-- The defect is quadratic. -/
theorem spanDefect_const_mul (S : Finset ℕ) (d : ℕ → ℝ) (c : ℝ) :
    D.spanDefect S (fun k => c * d k) = c ^ 2 * D.spanDefect S d := by
  unfold CurveDatum.spanDefect
  have h1 : ∑ k ∈ S, c * d k = c * ∑ k ∈ S, d k := (Finset.mul_sum _ _ _).symm
  have h2 : ∑ k ∈ S, c * d k * D.q ^ k = c * ∑ k ∈ S, d k * D.q ^ k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have h3 : ∑ k ∈ S, ∑ l ∈ S, c * d k * (c * d l) * D.graphPair k l =
      c ^ 2 * ∑ k ∈ S, ∑ l ∈ S, d k * d l * D.graphPair k l := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  rw [h1, h2, h3]
  ring

theorem continuous_spanDefect (S : Finset ℕ) : Continuous fun d : ℕ → ℝ => D.spanDefect S d := by
  unfold CurveDatum.spanDefect
  fun_prop

/-- The defect of an integral class. -/
def intSpanDefect (S : Finset ℕ) (d : ℕ → ℤ) : ℝ := D.spanDefect S fun k => (d k : ℝ)

theorem intSpanDefect_smul (S : Finset ℕ) (m : ℕ) (d : ℕ → ℤ) :
    intSpanDefect D S (m • d) = (m : ℝ) ^ 2 * intSpanDefect D S d := by
  unfold intSpanDefect
  rw [← spanDefect_const_mul]
  congr 1
  funext k
  simp

/-- **Hodge index on integral classes forces RH.** Rational classes reduce to integral ones by
homogeneity, and real classes are limits of rational ones. -/
theorem unitary_of_intSpanDefect_nonneg (h : ∀ S d, 0 ≤ intSpanDefect D S d) :
    ∀ i, ‖D.β i‖ = 1 := by
  refine (D.hodgeIndexOnSpan_iff_unitary).mp fun S d => ?_
  -- the rational approximants `⌊(j+1) d_k⌋/(j+1)`
  set a : ℕ → ℕ → ℝ := fun j k => (1 / ((j : ℝ) + 1)) * (⌊((j : ℝ) + 1) * d k⌋ : ℝ) with ha
  have hnonneg : ∀ j, 0 ≤ D.spanDefect S (a j) := by
    intro j
    have := h S fun k => ⌊((j : ℝ) + 1) * d k⌋
    rw [ha]
    simp only
    rw [spanDefect_const_mul]
    exact mul_nonneg (sq_nonneg _) this
  have hconv : Tendsto a atTop (𝓝 d) := by
    rw [tendsto_pi_nhds]
    intro k
    have hlow : ∀ j : ℕ, d k - 1 / ((j : ℝ) + 1) ≤ a j k := by
      intro j
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hfl := Int.sub_one_lt_floor (((j : ℝ) + 1) * d k)
      rw [ha]
      simp only
      rw [one_div, ← div_eq_inv_mul, le_div_iff₀ hj]
      have : (d k - ((j : ℝ) + 1)⁻¹) * ((j : ℝ) + 1) = ((j : ℝ) + 1) * d k - 1 := by
        field_simp
      linarith
    have hup : ∀ j : ℕ, a j k ≤ d k := by
      intro j
      have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
      have hfl := Int.floor_le (((j : ℝ) + 1) * d k)
      rw [ha]
      simp only
      rw [one_div, ← div_eq_inv_mul, div_le_iff₀ hj]
      linarith
    have hlim : Tendsto (fun j : ℕ => d k - 1 / ((j : ℝ) + 1)) atTop (𝓝 (d k)) := by
      simpa using tendsto_const_nhds.sub tendsto_one_div_add_atTop_nhds_zero_nat
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlim tendsto_const_nhds hlow hup
  exact ge_of_tendsto (((continuous_spanDefect D S).tendsto d).comp hconv)
    (Eventually.of_forall hnonneg)

/-- **The count door of a curve.** The integral Castelnuovo–Severi defect is the Tate limit of a
count on every span iff the datum is unitary. -/
theorem curve_countDoor :
    (∀ S : Finset ℕ, ∃ K : (ℕ → ℤ) → ℕ, ∀ d, Tendsto (fun m : ℕ => (K (m • d) : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 (intSpanDefect D S d))) ↔ ∀ i, ‖D.β i‖ = 1 := by
  constructor
  · intro h
    refine unitary_of_intSpanDefect_nonneg D fun S => ?_
    exact (exists_count_tateLimit_iff _ (intSpanDefect_smul D S)).mp (h S)
  · intro hU S
    refine (exists_count_tateLimit_iff _ (intSpanDefect_smul D S)).mpr fun d => ?_
    exact (D.hodgeIndexOnSpan_iff_unitary).mpr hU S _

end CurveDatum'

/-! ### On a true curve the form is a count -/

section Hyperelliptic

open ArithmeticEffectivityTheory Polynomial CurveDatum'

variable {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
  (hodd : Odd f.natDegree)

/-- The Lefschetz numbers of a true hyperelliptic curve are integers. -/
theorem hyperelliptic_pointCount_int (j : ℕ) :
    ∃ z : ℤ, (hyperellipticDatum hF hsq hodd).pointCount j = z := by
  rcases Nat.eq_zero_or_pos j with rfl | hj
  · exact ⟨2 - (Fintype.card (Fin (RHTower.Hyperelliptic.lRoots f).toList.length) : ℤ), by
      rw [CurveDatum.pointCount_zero]; push_cast; ring⟩
  · haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
    haveI : NeZero j := ⟨hj.ne'⟩
    let E := FiniteField.Extension F (ringChar F) j
    letI : Fintype E := Fintype.ofFinite E
    have hfin : Module.finrank F E = j := FiniteField.finrank_extension F (ringChar F) j
    have h := hyperellipticDatum_pointCount hF hsq hodd E
    rw [hfin] at h
    obtain ⟨c, hc⟩ : ∃ c : ℕ, (hyperellipticDatum hF hsq hodd).pointCount j = (c : ℝ) + 1 :=
      ⟨_, h⟩
    exact ⟨(c : ℤ) + 1, by rw [hc]; push_cast; ring⟩

/-- **On a true curve the defect is a count**: an integer polynomial in `q` and the point counts,
and a natural number on every integral class. -/
theorem hyperelliptic_spanDefect_is_count (S : Finset ℕ) :
    ∃ K : (ℕ → ℤ) → ℕ, ∀ d,
      (K d : ℝ) = intSpanDefect (hyperellipticDatum hF hsq hodd) S d ∧
        ∀ m : ℕ, K (m • d) = m ^ 2 * K d := by
  set D := hyperellipticDatum hF hsq hodd
  choose N hN using hyperelliptic_pointCount_int hF hsq hodd
  have hq : D.q = (Fintype.card F : ℝ) := rfl
  -- the integer value of the defect
  set Z : (ℕ → ℤ) → ℤ := fun d =>
    2 * (∑ k ∈ S, d k) * (∑ k ∈ S, d k * (Fintype.card F : ℤ) ^ k) -
      ∑ k ∈ S, ∑ l ∈ S, d k * d l * ((Fintype.card F : ℤ) ^ min k l * N (Nat.dist k l)) with hZ
  have hval : ∀ d, intSpanDefect D S d = (Z d : ℝ) := by
    intro d
    simp only [intSpanDefect, CurveDatum.spanDefect, CurveDatum.graphPair, hq, hZ, hN]
    push_cast
    ring
  have hnn : ∀ d, 0 ≤ Z d := by
    intro d
    have := (D.hodgeIndexOnSpan_iff_unitary).mpr (hyperellipticDatum_unitary hF hsq hodd) S
      (fun k => (d k : ℝ))
    have h' : (0 : ℝ) ≤ (Z d : ℝ) := by rw [← hval]; exact this
    exact_mod_cast h'
  refine ⟨fun d => (Z d).toNat, fun d => ⟨?_, fun m => ?_⟩⟩
  · rw [hval, Int.toNat_of_nonneg (hnn d)]
  · have hsm : (Z (m • d) : ℝ) = (m : ℝ) ^ 2 * (Z d : ℝ) := by
      rw [← hval, ← hval, intSpanDefect_smul]
    have hzi : Z (m • d) = (m : ℤ) ^ 2 * Z d := by exact_mod_cast hsm
    rw [hzi, Int.toNat_mul (by positivity) (hnn d)]
    simp

end Hyperelliptic

end GaloisForLFunctions.CountingHolography
