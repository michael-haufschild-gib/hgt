import GaloisForLFunctions.RHTower.BohrSetExistence

/-!
# The dense model of an arithmetic coefficient function

`classPush n S f` pushes a coefficient function `f` supported on a finite set `S` of integers
coprime to `q = n + 1` forward to `(ZMod q)ˣ`, by summing over each reduced residue class.  Its
Fourier coefficients are exactly the arithmetic character sums `∑_{k ∈ S} f k χ̄(k)`
(`unitFourier_classPush`), and it has the same total mass (`sum_classPush`).

Combining this with the group-side dense model results gives the arithmetic form of the
multiplicative dense model theorem of Matomäki--Teräväinen: `denseModel_arith_fourier` is the
Fourier identity, and `denseModel_arith_pointwise` is the pointwise bound (item (i)), where the
factor `K` is supplied by `exists_bohrSet` as `M^{#T}`.
-/

open Finset

noncomputable section

namespace RHTower

/-- Summing a function over the reduced residue classes recovers its sum over the elements of a
finite set of integers that are coprime to the modulus. -/
theorem sum_over_units_fibers' (n : ℕ) (S : Finset ℕ) (G : ℕ → ℂ) :
    ∑ u : (ZMod (n + 1))ˣ,
        ∑ k ∈ S.filter (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))), G k
      = ∑ k ∈ S, (if IsUnit (Nat.cast k : ZMod (n + 1)) then G k else 0) := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  by_cases hk : IsUnit (Nat.cast k : ZMod (n + 1))
  · rw [if_pos hk]
    have hsingle : ∀ u ∈ (Finset.univ : Finset (ZMod (n + 1))ˣ), u ≠ hk.unit →
        (if (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1)) then G k else 0) = 0 := by
      intro u _ hune
      have hne : (Nat.cast k : ZMod (n + 1)) ≠ (u : ZMod (n + 1)) := by
        intro heq
        apply hune
        apply Units.ext
        rw [← heq, IsUnit.unit_spec]
      simp [hne]
    have hmem : hk.unit ∉ (Finset.univ : Finset (ZMod (n + 1))ˣ) →
        (if (Nat.cast k : ZMod (n + 1)) = ((hk.unit : (ZMod (n + 1))ˣ) : ZMod (n + 1))
          then G k else 0) = 0 := fun h => absurd (Finset.mem_univ _) h
    rw [Finset.sum_eq_single hk.unit hsingle hmem, IsUnit.unit_spec]
    simp
  · rw [if_neg hk]
    refine Finset.sum_eq_zero (fun u _ => ?_)
    have hne : (Nat.cast k : ZMod (n + 1)) ≠ (u : ZMod (n + 1)) := by
      intro heq
      exact hk (heq ▸ u.isUnit)
    simp [hne]

/-- The pushforward of a coefficient function on integers to the unit group. -/
def classPush (n : ℕ) (S : Finset ℕ) (f : ℕ → ℝ) (u : (ZMod (n + 1))ˣ) : ℝ :=
  ∑ k ∈ S.filter (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))), f k

/-- The Fourier coefficients of the pushforward are the arithmetic character sums. -/
theorem unitFourier_classPush (n : ℕ) (S : Finset ℕ) (f : ℕ → ℝ)
    (hS : ∀ k ∈ S, IsUnit (Nat.cast k : ZMod (n + 1))) (χ : DirichletCharacter ℂ (n + 1)) :
    unitFourier n (classPush n S f) χ
      = ∑ k ∈ S, ((f k : ℝ) : ℂ) * (starRingEnd ℂ) (χ (Nat.cast k : ZMod (n + 1))) := by
  classical
  rw [unitFourier]
  have hstep : ∀ u : (ZMod (n + 1))ˣ,
      ((classPush n S f u : ℝ) : ℂ) * (starRingEnd ℂ) (χ (u : ZMod (n + 1)))
        = ∑ k ∈ S.filter (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))),
            ((f k : ℝ) : ℂ) * (starRingEnd ℂ) (χ (Nat.cast k : ZMod (n + 1))) := by
    intro u
    rw [classPush, Complex.ofReal_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [(Finset.mem_filter.1 hk).2]
  rw [Finset.sum_congr rfl (fun u _ => hstep u), sum_over_units_fibers']
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [if_pos (hS k hk)]

/-- The pushforward preserves the total mass. -/
theorem sum_classPush (n : ℕ) (S : Finset ℕ) (f : ℕ → ℝ)
    (hS : ∀ k ∈ S, IsUnit (Nat.cast k : ZMod (n + 1))) :
    ∑ u : (ZMod (n + 1))ˣ, classPush n S f u = ∑ k ∈ S, f k := by
  classical
  have h := sum_over_units_fibers' n S (fun k => ((f k : ℝ) : ℂ))
  have hL : ((∑ u : (ZMod (n + 1))ˣ, classPush n S f u : ℝ) : ℂ)
      = ∑ u : (ZMod (n + 1))ˣ,
          ∑ k ∈ S.filter (fun k : ℕ => (Nat.cast k : ZMod (n + 1)) = (u : ZMod (n + 1))),
            ((f k : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun u _ => by rw [classPush, Complex.ofReal_sum])
  have hR : ∑ k ∈ S, (if IsUnit (Nat.cast k : ZMod (n + 1)) then ((f k : ℝ) : ℂ) else 0)
      = ((∑ k ∈ S, f k : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl (fun k hk => by rw [if_pos (hS k hk)])
  have : ((∑ u : (ZMod (n + 1))ˣ, classPush n S f u : ℝ) : ℂ) = ((∑ k ∈ S, f k : ℝ) : ℂ) := by
    rw [hL, h, hR]
  exact_mod_cast this


theorem classPush_nonneg (n : ℕ) (S : Finset ℕ) (f : ℕ → ℝ) (hf : ∀ k ∈ S, 0 ≤ f k)
    (u : (ZMod (n + 1))ˣ) : 0 ≤ classPush n S f u := by
  classical
  rw [classPush]
  exact Finset.sum_nonneg (fun k hk => hf k (Finset.mem_filter.1 hk).1)

theorem denseModel_nonneg (n : ℕ) (F : (ZMod (n + 1))ˣ → ℝ) (hF : ∀ u, 0 ≤ F u)
    (B : Finset (ZMod (n + 1))ˣ) (a : (ZMod (n + 1))ˣ) : 0 ≤ denseModel n F B a := by
  rw [denseModel]
  apply mul_nonneg
  · positivity
  · exact Finset.sum_nonneg (fun b₁ _ => Finset.sum_nonneg (fun b₂ _ => hF _))

/-- **The arithmetic form of the dense model Fourier identity.**  The model's Fourier coefficients
are the arithmetic character sums of `f`, scaled by `‖E_{b ∈ B} χ(b)‖²`. -/
theorem denseModel_arith_fourier (n : ℕ) (S : Finset ℕ) (f : ℕ → ℝ)
    (hS : ∀ k ∈ S, IsUnit (Nat.cast k : ZMod (n + 1)))
    (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty) (χ : DirichletCharacter ℂ (n + 1)) :
    ((((n + 1).totient : ℂ))⁻¹ * ∑ a : (ZMod (n + 1))ˣ,
        ((denseModel n (classPush n S f) B a : ℝ) : ℂ)
          * (starRingEnd ℂ) (χ (a : ZMod (n + 1))))
      = ((‖bohrAvg n B χ‖ ^ 2 : ℝ) : ℂ)
        * ∑ k ∈ S, ((f k : ℝ) : ℂ) * (starRingEnd ℂ) (χ (Nat.cast k : ZMod (n + 1))) := by
  rw [denseModel_fourier_real n (classPush n S f) B hB χ, unitFourier_classPush n S f hS χ]

/-- **The arithmetic form of item (i).**  If every nonprincipal arithmetic character sum of `f` is
at most `M₀`, then the model stays within `M₀ · M^{#T}` of the total mass of `f`, for any Bohr set
`B` obtained from `exists_bohrSet`. -/
theorem denseModel_arith_pointwise (n : ℕ) (S : Finset ℕ) (f : ℕ → ℝ)
    (hS : ∀ k ∈ S, IsUnit (Nat.cast k : ZMod (n + 1)))
    (B : Finset (ZMod (n + 1))ˣ) (hB : B.Nonempty)
    {M₀ K : ℝ} (hM₀ : 0 ≤ M₀)
    (hsize : (((n + 1).totient : ℝ)) ≤ K * (B.card : ℝ))
    (hsmall : ∀ χ : DirichletCharacter ℂ (n + 1), χ ≠ 1 →
      ‖∑ k ∈ S, ((f k : ℝ) : ℂ) * (starRingEnd ℂ) (χ (Nat.cast k : ZMod (n + 1)))‖ ≤ M₀)
    (a : (ZMod (n + 1))ˣ) :
    |denseModel n (classPush n S f) B a - ∑ k ∈ S, f k| ≤ M₀ * K := by
  have hBpos : (0 : ℝ) < (B.card : ℝ) := by exact_mod_cast Finset.card_pos.2 hB
  have hsmall' : ∀ χ : DirichletCharacter ℂ (n + 1), χ ≠ 1 →
      ‖unitFourier n (classPush n S f) χ‖ ≤ M₀ := by
    intro χ hχ
    rw [unitFourier_classPush n S f hS χ]
    exact hsmall χ hχ
  have hmain := norm_denseModel_sub_mass_le n (classPush n S f) B hB hM₀ hsmall' a
  rw [sum_classPush n S f hS] at hmain
  refine le_trans hmain ?_
  have hratio : (((n + 1).totient : ℝ)) / (B.card : ℝ) ≤ K := by
    rw [div_le_iff₀ hBpos]
    exact hsize
  exact mul_le_mul_of_nonneg_left hratio hM₀

end RHTower
