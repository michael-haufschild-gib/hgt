import GaloisForLFunctions.HTGeometry.SubsetSumExpFamily
import GaloisForLFunctions.HTGeometry.ExpRelationNoGo
import GaloisForLFunctions.HTGeometry.LinearVersusAlgebraicCollapse

/-!
# The exponential of a nonzero algebraic number is not an integer

Hermite–Lindemann in the form needed for the logarithm of an integer: if `α` is algebraic then
`exp α` is not an integer of absolute value at least two.  Consequently `log q` is transcendental
for every integer `q ≥ 2`.

The proof symmetrises.  Let `α` be a root of the monic integer polynomial `m` of degree `n`, with
complex roots `ρ₁, …, ρₙ`, and suppose `exp α = Q`.  Then `∏ᵢ (exp (n ρᵢ) − Qⁿ) = 0`, because the
factor belonging to `α` vanishes.  Expanding the product turns it into
`∑_{S ⊆ {1,…,n}} (−Qⁿ)^{n−|S|} exp (n γ_S)` with `γ_S = ∑_{i ∈ S} ρᵢ`.  For each size `s` the
numbers `n γ_S` with `|S| = s` are the roots of a monic integer polynomial, because the family of
formal subset sums is invariant under renaming the roots; splitting off the largest power of `X`
separates the vanishing subset sums, which contribute a constant, from the rest.  The result is a
relation `b + ∑_s β_s ∑_{r} exp r = 0` of exactly the shape `no_int_grouped_exp_relation` forbids,
and the scaling by `n` is what makes the constant `b` nonzero: its `S = ∅` term has size `Q^{n·n}`
while the at most `2ⁿ` remaining terms have size at most `Q^{n(n−1)}`.

* `exp_ne_intCast_of_monic_root` — the case of an algebraic integer.
* `exp_ne_intCast_of_isAlgebraic` — the general case, by scaling to an algebraic integer.
* `transcendental_log_natCast` — `Real.log q` is transcendental for `q ≥ 2`.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial Finset

/-- **The exponential of a root of a monic integer polynomial is not an integer `≥ 2`.** -/
theorem exp_ne_intCast_of_monic_root {α : ℂ} {m : ℤ[X]} (hm : m.Monic)
    (hroot : Polynomial.aeval α m = 0) {Q : ℤ} (hQ : 2 ≤ Q) :
    Complex.exp α ≠ (Q : ℂ) := by
  classical
  intro hexp
  obtain ⟨n, hn⟩ : ∃ n, m.natDegree = n := ⟨_, rfl⟩
  have hn1 : 1 ≤ n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · exfalso
      rw [h] at hn
      rw [eq_one_of_monic_natDegree_zero hm hn] at hroot
      simp at hroot
    · exact h
  -- index the complex roots of `m`
  have hmapdeg : (m.map (algebraMap ℤ ℂ)).natDegree = m.natDegree := hm.natDegree_map _
  have hcard : Multiset.card (m.aroots ℂ) = n := by
    rw [Polynomial.aroots, ← hn, ← hmapdeg]
    exact Polynomial.splits_iff_card_roots.mp (IsAlgClosed.splits _)
  obtain ⟨ρ, hρ⟩ := exists_index_of_multiset (m.aroots ℂ) n hcard
  have hαmem : α ∈ m.aroots ℂ := by
    rw [Polynomial.mem_aroots]
    exact ⟨hm.ne_zero, hroot⟩
  obtain ⟨i₀, hi₀⟩ : ∃ i : Fin n, ρ i = α := by
    rw [hρ, Multiset.mem_map] at hαmem
    obtain ⟨i, -, hi⟩ := hαmem
    exact ⟨i, hi⟩
  obtain ⟨Rz, hRzdef⟩ : ∃ r : ℤ, r = Q ^ n := ⟨_, rfl⟩
  have hRpos : (0 : ℤ) < Rz := by rw [hRzdef]; exact pow_pos (by linarith) n
  have hR1 : (1 : ℤ) ≤ Rz := by omega
  have hR2n : (2 : ℤ) ^ n ≤ Rz := by rw [hRzdef]; exact pow_le_pow_left₀ (by norm_num) hQ n
  -- the monic integer polynomials carrying the scaled subset sums of each size
  choose F hFmonic hFdeg hFroots0 using fun j : ℕ =>
    exists_monic_subsetSum_poly hm hn hρ (n : ℤ) j
  have hFroots : ∀ j : ℕ, (F j).aroots ℂ
      = ((Finset.powersetCard j (Finset.univ : Finset (Fin n))).val).map
        (fun S => ((n : ℕ) : ℂ) * ∑ i ∈ S, ρ i) := by
    intro j
    rw [hFroots0 j]
    simp only [Int.cast_natCast]
  choose z H hHmonic hHeval hFsplit hzle using fun j : ℕ =>
    exists_monic_nonzero_const_factor (hFmonic j)
  have hSexp : ∀ j : ℕ, ∑ t ∈ Finset.powersetCard j (Finset.univ : Finset (Fin n)),
      Complex.exp ((n : ℂ) * ∑ i ∈ t, ρ i)
      = (z j : ℂ) + (((H j).aroots ℂ).map Complex.exp).sum := by
    intro j
    rw [← sum_exp_aroots_of_eq_X_pow_mul (hFmonic j) (hFsplit j), hFroots j, Multiset.map_map]
    rfl
  -- the vanishing product, expanded over the subsets
  have hprodzero : ∏ i : Fin n, (Complex.exp ((n : ℂ) * ρ i) - ((Rz : ℤ) : ℂ)) = 0 := by
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    rw [hi₀, Complex.exp_nat_mul, hexp, hRzdef]
    push_cast
    ring
  have hkey : ∑ t ∈ (Finset.univ : Finset (Fin n)).powerset,
      Complex.exp ((n : ℂ) * ∑ i ∈ t, ρ i) * (-((Rz : ℤ) : ℂ)) ^ (n - t.card) = 0 := by
    rw [← hprodzero]
    have hfun : (fun i : Fin n => Complex.exp ((n : ℂ) * ρ i) - ((Rz : ℤ) : ℂ))
        = (fun i : Fin n => Complex.exp ((n : ℂ) * ρ i) + (-((Rz : ℤ) : ℂ))) := by
      funext i; ring
    rw [hfun, Finset.prod_add]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.prod_const, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      Fintype.card_fin]
    congr 1
    rw [Finset.mul_sum, Complex.exp_sum]
  rw [Finset.sum_powerset] at hkey
  simp only [Finset.card_univ, Fintype.card_fin] at hkey
  have hkey2 : ∑ j ∈ Finset.range (n + 1), (-((Rz : ℤ) : ℂ)) ^ (n - j) *
      ((z j : ℂ) + (((H j).aroots ℂ).map Complex.exp).sum) = 0 := by
    rw [← hkey]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hSexp j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t ht => ?_
    rw [Finset.mem_powersetCard] at ht
    rw [ht.2, mul_comm]
  -- the integer coefficients of the grouped relation
  obtain ⟨βz, hβz⟩ : ∃ f : ℕ → ℤ, ∀ j, f j = (-Rz) ^ (n - j) := ⟨_, fun _ => rfl⟩
  obtain ⟨bz, hbzdef⟩ : ∃ b : ℤ, b = ∑ j ∈ Finset.range (n + 1), βz j * (z j : ℤ) := ⟨_, rfl⟩
  have hβc : ∀ j : ℕ, ((βz j : ℤ) : ℂ) = (-((Rz : ℤ) : ℂ)) ^ (n - j) := by
    intro j
    rw [hβz]
    push_cast
    ring
  have hfinal : (bz : ℂ) + ∑ j : Fin (n + 1), ((βz (j : ℕ) : ℤ) : ℂ) *
      ((((H (j : ℕ)).aroots ℂ)).map Complex.exp).sum = 0 := by
    rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => ((βz j : ℤ) : ℂ) * ((((H j).aroots ℂ)).map Complex.exp).sum) (n + 1)]
    have hb1 : (bz : ℂ) = ∑ j ∈ Finset.range (n + 1), ((βz j : ℤ) : ℂ) * (z j : ℂ) := by
      rw [hbzdef]; push_cast; ring
    rw [hb1, ← Finset.sum_add_distrib]
    refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) hkey2
    rw [hβc j]
    ring
  -- the constant term is nonzero
  have hF0eval : (F 0).eval (0 : ℤ) = 0 := by
    have hmem : (0 : ℂ) ∈ (F 0).aroots ℂ := by
      rw [hFroots 0, Finset.powersetCard_zero]
      simp
    rw [Polynomial.mem_aroots] at hmem
    have h2 := hmem.2
    rw [Polynomial.aeval_def, Polynomial.eval₂_at_zero] at h2
    have h3 : (F 0).coeff 0 = 0 := by simpa using h2
    rwa [Polynomial.coeff_zero_eq_eval_zero] at h3
  have hz0 : 1 ≤ z 0 := by
    rw [Nat.one_le_iff_ne_zero]
    intro h
    have hs := hFsplit 0
    rw [h, pow_zero, one_mul] at hs
    rw [hs] at hF0eval
    exact hHeval 0 hF0eval
  have hzsum : ∑ j ∈ Finset.range (n + 1), z j ≤ 2 ^ n := by
    calc ∑ j ∈ Finset.range (n + 1), z j
        ≤ ∑ j ∈ Finset.range (n + 1), n.choose j :=
          Finset.sum_le_sum fun j _ => by have := hzle j; rwa [hFdeg j] at this
      _ = 2 ^ n := Nat.sum_range_choose n
  have hbne : bz ≠ 0 := by
    intro hzero
    rw [hbzdef, Finset.sum_range_succ'] at hzero
    have hβ0 : βz 0 = (-Rz) ^ n := by rw [hβz]; simp
    rw [hβ0] at hzero
    have htail : |∑ i ∈ Finset.range n, βz (i + 1) * (z (i + 1) : ℤ)|
        ≤ Rz ^ (n - 1) * ((2 : ℤ) ^ n - 1) := by
      refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
      have hterm : ∀ i ∈ Finset.range n, |βz (i + 1) * (z (i + 1) : ℤ)|
          ≤ Rz ^ (n - 1) * (z (i + 1) : ℤ) := by
        intro i hi
        rw [Finset.mem_range] at hi
        rw [hβz, abs_mul, abs_pow, abs_neg, abs_of_pos hRpos,
          abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((z (i + 1) : ℕ) : ℤ))]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hR1 (by omega)) (by positivity)
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      have h1 : (∑ i ∈ Finset.range n, z (i + 1)) + z 0 ≤ 2 ^ n := by
        rw [← Finset.sum_range_succ']; exact hzsum
      have hnat : (∑ i ∈ Finset.range n, z (i + 1)) + 1 ≤ 2 ^ n := le_trans (by omega) h1
      have hZ : ((∑ i ∈ Finset.range n, z (i + 1) : ℕ) : ℤ) + 1 ≤ (2 : ℤ) ^ n := by
        exact_mod_cast hnat
      push_cast at hZ
      linarith
    have hmain : Rz ^ n ≤ |(-Rz) ^ n * (z 0 : ℤ)| := by
      rw [abs_mul, abs_pow, abs_neg, abs_of_pos hRpos,
        abs_of_nonneg (by positivity : (0 : ℤ) ≤ ((z 0 : ℕ) : ℤ))]
      exact le_mul_of_one_le_right (pow_pos hRpos n).le (by exact_mod_cast hz0)
    have heq : ∑ i ∈ Finset.range n, βz (i + 1) * (z (i + 1) : ℤ)
        = -((-Rz) ^ n * (z 0 : ℤ)) := by linarith [hzero]
    rw [heq, abs_neg] at htail
    have hpow : Rz ^ (n - 1) * Rz = Rz ^ n := by
      rw [← pow_succ]
      congr 1
      omega
    have hpos : (0 : ℤ) < Rz ^ (n - 1) := pow_pos hRpos _
    have hlt : Rz ^ (n - 1) * ((2 : ℤ) ^ n - 1) < Rz ^ n := by
      linarith [mul_le_mul_of_nonneg_left hR2n hpos.le]
    linarith [hmain, htail, hlt]
  -- contradiction with the grouped Lindemann–Weierstrass core
  refine no_int_grouped_exp_relation (H := fun j : Fin (n + 1) => H (j : ℕ))
    (fun j => hHmonic _) ?_ (fun j : Fin (n + 1) => βz (j : ℕ)) hbne hfinal
  rw [Polynomial.eval_prod]
  exact Finset.prod_ne_zero_iff.mpr fun j _ => hHeval _

/-- **Hermite–Lindemann for integer values: the exponential of an algebraic number is not an
integer of absolute value at least two.** -/
theorem exp_ne_intCast_of_isAlgebraic {α : ℂ} (hα : IsAlgebraic ℤ α) {Q : ℤ} (hQ : 2 ≤ Q) :
    Complex.exp α ≠ (Q : ℂ) := by
  classical
  intro hexp
  obtain ⟨g₀, hg₀ne, hg₀⟩ := hα
  -- normalise the leading coefficient to be positive
  obtain ⟨g, hgne, hg, hglead⟩ : ∃ g : ℤ[X], g ≠ 0 ∧ Polynomial.aeval α g = 0
      ∧ 0 < g.leadingCoeff := by
    rcases lt_trichotomy g₀.leadingCoeff 0 with h | h | h
    · exact ⟨-g₀, neg_ne_zero.mpr hg₀ne, by rw [map_neg, hg₀, neg_zero], by
        rw [Polynomial.leadingCoeff_neg]; linarith⟩
    · exact absurd h (Polynomial.leadingCoeff_ne_zero.mpr hg₀ne)
    · exact ⟨g₀, hg₀ne, hg₀, h⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ, (d : ℤ) = g.leadingCoeff := ⟨g.leadingCoeff.toNat, by omega⟩
  have hd1 : 1 ≤ d := by omega
  -- `d · α` is a root of a monic integer polynomial
  have hmonic : g.integralNormalization.Monic := Polynomial.monic_integralNormalization hgne
  have hroot : Polynomial.aeval ((algebraMap ℤ ℂ) g.leadingCoeff * α) g.integralNormalization = 0 :=
    Polynomial.integralNormalization_aeval_eq_zero hg (fun x hx => by simpa using hx)
  have hscale : (algebraMap ℤ ℂ) g.leadingCoeff * α = (d : ℂ) * α := by
    rw [← hd]; simp
  rw [hscale] at hroot
  -- and its exponential is `Q ^ d`
  have hexpd : Complex.exp ((d : ℂ) * α) = ((Q ^ d : ℤ) : ℂ) := by
    rw [Complex.exp_nat_mul, hexp]
    push_cast
    ring
  have hQd : 2 ≤ Q ^ d := by
    calc (2 : ℤ) = 2 ^ 1 := by norm_num
      _ ≤ Q ^ d := by
          refine le_trans (pow_le_pow_right₀ (by norm_num) hd1) ?_
          exact pow_le_pow_left₀ (by norm_num) hQ d
  exact exp_ne_intCast_of_monic_root hmonic hroot hQd hexpd

/-- **The logarithm of an integer `q ≥ 2` is transcendental.** -/
theorem transcendental_log_natCast {q : ℕ} (hq : 2 ≤ q) : Transcendental ℚ (Real.log q) := by
  intro halg
  have hZ : IsAlgebraic ℤ (Real.log q) := by
    by_contra h
    exact ((Algebra.IsAlgebraic.transcendental_iff (R := ℤ) (S := ℚ)).mp h) halg
  have hC : IsAlgebraic ℤ ((Real.log q : ℝ) : ℂ) := by
    obtain ⟨p, hp0, hp⟩ := hZ
    refine ⟨p, hp0, ?_⟩
    have hc : ((Real.log q : ℝ) : ℂ) = algebraMap ℝ ℂ (Real.log q) := rfl
    rw [hc, Polynomial.aeval_algebraMap_apply, hp, map_zero]
  refine exp_ne_intCast_of_isAlgebraic hC (Q := (q : ℤ)) (by exact_mod_cast hq) ?_
  rw [← Complex.ofReal_exp, Real.exp_log (by positivity)]
  push_cast
  ring

end GaloisForLFunctions.HTGeometry
