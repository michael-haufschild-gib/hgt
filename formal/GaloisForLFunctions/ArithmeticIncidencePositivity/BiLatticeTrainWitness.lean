import GaloisForLFunctions.ArithmeticIncidencePositivity.ResonantTrainWitness

/-!
# The bi-lattice train: two towers resonate at once

The single-tower sector is closed: both the arithmetic envelope and its parity twin are attained by
trains on one multiplicative progression. The cross-tower sector needs a test aligned with **two**
primes at once, and that is the **bi-lattice train**: unit copies of one bump at the shifts

    S = { i a + j b : i, j < M },     a = log p,  b = log q,

the logarithms of the `{p, q}`-smooth numbers of a square box. Since the logarithms of distinct
primes are `ℤ`-independent, the lag `k a` is matched exactly by the lattice pairs that differ by `k`
in the first exponent and agree in the second, so

    A_S(k a) = (M − k) · M · A_g(0),     A_S(0) = M² · A_g(0),

and symmetrically in `b`. Both towers therefore resonate to the full fraction `(M − k)/M → 1`: the
**two Euler envelopes add**, so the prime-side bound is sharp already on a pair of aligned towers,
and the cross lags `log(p^i/q^j)` carry positive counts. In particular the cross-prime aggregate of
an aligned test is strictly positive, so the polynomial regime of the comb-energy reduction, which
needs a nonpositive aggregate, fails exactly on the multiplicatively aligned tests — the ones where
the cost side is large.
-/

open MeasureTheory Set
open GaloisForLFunctions.ArithmeticCriticalityTheory

noncomputable section

namespace GaloisForLFunctions.ArithmeticIncidencePositivity

variable {g : ℝ → ℝ}

/-- The bi-lattice train: unit copies of `g` at the shifts `i a + j b`, `i, j < M`. -/
def biLatticeTrain (g : ℝ → ℝ) (a b : ℝ) (M : ℕ) : ℝ → ℝ :=
  finsetComb g (Finset.range M ×ˢ Finset.range M) (fun _ => 1)
    (fun z => (z.1 : ℝ) * a + (z.2 : ℝ) * b)

/-- **The resonance of the bi-lattice train at a first-generator lag.** For independent generators
whose nonzero small integer combinations are separated beyond the bump diameter, the train's
autocorrelation at `k a` counts the matching lattice pairs: `(M − k) M` of the `M²` copies. -/
theorem autoCorr_biLatticeTrain_fst {a b w : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hw : 0 ≤ w) (hsupp : ∀ x, w < |x| → g x = 0) {M k : ℕ} (hk : k ≤ M)
    (hind : ∀ u v : ℤ, (u : ℝ) * a + (v : ℝ) * b = 0 → u = 0 ∧ v = 0)
    (hsep : ∀ u v : ℤ, |u| ≤ 2 * (M : ℤ) → |v| ≤ (M : ℤ) →
      ((u : ℝ) * a + (v : ℝ) * b ≠ 0) → 2 * w < |(u : ℝ) * a + (v : ℝ) * b|) :
    autoCorr (biLatticeTrain g a b M) ((k : ℝ) * a)
      = (((M - k : ℕ) : ℝ) * (M : ℝ)) * autoCorr g 0 := by
  have hgn : ContCompact g := ⟨hg, hgc⟩
  obtain ⟨R, hR⟩ : ∃ R : Finset (ℕ × ℕ), R = Finset.range M ×ˢ Finset.range M := ⟨_, rfl⟩
  obtain ⟨d, hd⟩ : ∃ d : ℕ × ℕ → ℝ, d = fun z => (z.1 : ℝ) * a + (z.2 : ℝ) * b := ⟨_, rfl⟩
  -- the Gram expansion of the train at the lag
  have hexp : autoCorr (biLatticeTrain g a b M) ((k : ℝ) * a)
      = ∑ z ∈ R, ∑ z' ∈ R, autoCorr g (d z' + (k : ℝ) * a - d z) := by
    rw [autoCorr_eq_testPairing,
      show biLatticeTrain g a b M = finsetComb g R (fun _ => 1) d by rw [hR, hd]; rfl,
      show (fun u => finsetComb g R (fun _ => 1) d (u + (k : ℝ) * a))
          = finsetComb g R (fun _ => 1) (fun z => d z + (k : ℝ) * a) by
        funext u
        refine Finset.sum_congr rfl fun z _ => ?_
        rw [show u + (k : ℝ) * a + d z = u + (d z + (k : ℝ) * a) by ring],
      testPairing_finsetComb hgn]
    exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => by
      rw [one_mul, one_mul]
  -- a pair contributes the mass exactly when it matches the lag
  have hterm : ∀ z ∈ R, ∀ z' ∈ R,
      autoCorr g (d z' + (k : ℝ) * a - d z)
        = if z'.1 + k = z.1 ∧ z.2 = z'.2 then autoCorr g 0 else 0 := by
    intro z hz z' hz'
    rw [hR, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hz hz'
    have hval : d z' + (k : ℝ) * a - d z
        = (((z'.1 : ℤ) + (k : ℤ) - (z.1 : ℤ) : ℤ) : ℝ) * a
          + (((z'.2 : ℤ) - (z.2 : ℤ) : ℤ) : ℝ) * b := by
      rw [hd]
      push_cast
      ring
    by_cases h : z'.1 + k = z.1 ∧ z.2 = z'.2
    · rw [if_pos h, hval]
      have h1 : ((z'.1 : ℤ) + (k : ℤ) - (z.1 : ℤ)) = 0 := by
        have := h.1; omega
      have h2 : ((z'.2 : ℤ) - (z.2 : ℤ)) = 0 := by
        have := h.2; omega
      rw [h1, h2]
      norm_num
    · rw [if_neg h, hval]
      refine autoCorr_eq_zero_of_support hsupp ?_
      have hne : (((z'.1 : ℤ) + (k : ℤ) - (z.1 : ℤ) : ℤ) : ℝ) * a
          + (((z'.2 : ℤ) - (z.2 : ℤ) : ℤ) : ℝ) * b ≠ 0 := by
        intro hc
        obtain ⟨hu, hv⟩ := hind _ _ hc
        exact h ⟨by omega, by omega⟩
      refine hsep _ _ ?_ ?_ hne
      · have h1 := hz.1
        have h2 := hz'.1
        rw [abs_le]
        constructor <;> omega
      · have h1 := hz.2
        have h2 := hz'.2
        rw [abs_le]
        constructor <;> omega
  rw [hexp, Finset.sum_congr rfl fun z hz => Finset.sum_congr rfl fun z' hz' =>
    hterm z hz z' hz', hR, Finset.sum_product]
  -- for each lattice point, at most one partner matches, and only if its index is at least `k`
  have hinner : ∀ i ∈ Finset.range M, ∀ j ∈ Finset.range M,
      ∑ z' ∈ Finset.range M ×ˢ Finset.range M,
          (if z'.1 + k = i ∧ j = z'.2 then autoCorr g 0 else 0)
        = if k ≤ i then autoCorr g 0 else 0 := by
    intro i hi j hj
    rw [Finset.sum_product]
    have hrow : ∀ i' ∈ Finset.range M,
        ∑ j' ∈ Finset.range M, (if i' + k = i ∧ j = j' then autoCorr g 0 else 0)
          = if i' + k = i then autoCorr g 0 else 0 := by
      intro i' _
      by_cases h1 : i' + k = i
      · rw [if_pos h1, Finset.sum_eq_single_of_mem j hj (fun b _ hb => by
          rw [if_neg (by tauto)])]
        rw [if_pos ⟨h1, rfl⟩]
      · rw [if_neg h1]
        exact Finset.sum_eq_zero fun j' _ => by rw [if_neg (by tauto)]
    rw [Finset.sum_congr rfl hrow]
    by_cases h2 : k ≤ i
    · rw [if_pos h2]
      have hmem : i - k ∈ Finset.range M := by
        rw [Finset.mem_range] at hi ⊢
        omega
      rw [Finset.sum_eq_single_of_mem (i - k) hmem (fun b _ hb => by
        rw [if_neg (by omega)])]
      rw [if_pos (by omega)]
    · rw [if_neg h2]
      refine Finset.sum_eq_zero fun i' _ => ?_
      rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun j hj => hinner i hi j hj]
  -- `M − k` first indices match, each with all `M` second indices
  have hfst : ∑ i ∈ Finset.range M, (if k ≤ i then autoCorr g 0 else 0)
      = ((M - k : ℕ) : ℝ) * autoCorr g 0 := by
    rw [← Finset.sum_filter]
    have hfilter : (Finset.range M).filter (fun i => k ≤ i) = Finset.Ico k M := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
      exact ⟨fun h => ⟨h.2, h.1⟩, fun h => ⟨h.2, h.1⟩⟩
    rw [hfilter, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  calc ∑ i ∈ Finset.range M, ∑ _j ∈ Finset.range M, (if k ≤ i then autoCorr g 0 else 0)
      = ∑ i ∈ Finset.range M, (M : ℝ) * (if k ≤ i then autoCorr g 0 else 0) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    _ = (M : ℝ) * ∑ i ∈ Finset.range M, (if k ≤ i then autoCorr g 0 else 0) := by
        rw [Finset.mul_sum]
    _ = (((M - k : ℕ) : ℝ) * (M : ℝ)) * autoCorr g 0 := by
        rw [hfst]; ring

/-! ### The hypotheses have a model: two distinct primes -/

/-- **Independence of two prime logarithms.** For distinct primes no nonzero integer combination of
`log p` and `log q` vanishes — unique factorization, in the corpus's `ℤ`-independence form. -/
theorem logPrime_pair_independent {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (u v : ℤ) (h : (u : ℝ) * Real.log p + (v : ℝ) * Real.log q = 0) : u = 0 ∧ v = 0 := by
  classical
  obtain ⟨f, hf⟩ : ∃ f : Fin 2 → Nat.Primes,
      f = fun i => if i = 0 then (⟨p, hp⟩ : Nat.Primes) else ⟨q, hq⟩ := ⟨_, rfl⟩
  have hfinj : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [hf] <;>
      exact absurd (congrArg Subtype.val hij) (by simpa using hpq)
  have hli : LinearIndependent ℤ (fun i : Fin 2 => Real.log ((f i : ℕ) : ℝ)) :=
    GaloisForLFunctions.logPrime_linearIndependent_int.comp f hfinj
  have hpair : LinearIndependent ℤ ![Real.log ((p : ℕ) : ℝ), Real.log ((q : ℕ) : ℝ)] := by
    have hfun : (fun i : Fin 2 => Real.log ((f i : ℕ) : ℝ))
        = ![Real.log ((p : ℕ) : ℝ), Real.log ((q : ℕ) : ℝ)] := by
      funext i
      fin_cases i <;> simp [hf]
    rwa [hfun] at hli
  have := (LinearIndependent.pair_iff.mp hpair) u v (by
    rw [zsmul_eq_mul, zsmul_eq_mul]
    exact h)
  exact this

/-- **A valid bump width exists.** For distinct primes and every box size the finitely many nonzero
integer combinations of the two logarithms have a positive minimum, so some bump is narrow enough
for the separation hypothesis. -/
theorem exists_width_biLattice_sep {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (M : ℕ) :
    ∃ w : ℝ, 0 < w ∧ ∀ u v : ℤ, |u| ≤ 2 * (M : ℤ) → |v| ≤ (M : ℤ) →
      ((u : ℝ) * Real.log p + (v : ℝ) * Real.log q ≠ 0) →
      2 * w < |(u : ℝ) * Real.log p + (v : ℝ) * Real.log q| := by
  classical
  obtain ⟨val, hval⟩ : ∃ val : ℤ × ℤ → ℝ,
      val = fun z => (z.1 : ℝ) * Real.log p + (z.2 : ℝ) * Real.log q := ⟨_, rfl⟩
  obtain ⟨B, hB⟩ : ∃ B : Finset (ℤ × ℤ),
      B = Finset.Icc (-(2 * (M : ℤ))) (2 * (M : ℤ)) ×ˢ Finset.Icc (-(M : ℤ)) (M : ℤ) := ⟨_, rfl⟩
  obtain ⟨V, hV⟩ : ∃ V : Finset ℝ,
      V = (B.filter (fun z => val z ≠ 0)).image (fun z => |val z|) := ⟨_, rfl⟩
  by_cases hne : V.Nonempty
  · refine ⟨V.min' hne / 3, ?_, ?_⟩
    · have hmem := V.min'_mem hne
      rw [hV, Finset.mem_image] at hmem
      obtain ⟨z, hz, hzeq⟩ := hmem
      rw [Finset.mem_filter] at hz
      have : 0 < |val z| := abs_pos.mpr hz.2
      rw [← hzeq] at this ⊢
      linarith
    · intro u v hu hv hnz
      have hmemB : (u, v) ∈ B := by
        rw [hB, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        rw [abs_le] at hu hv
        exact ⟨⟨hu.1, hu.2⟩, ⟨hv.1, hv.2⟩⟩
      have hmemV : |val (u, v)| ∈ V := by
        rw [hV, Finset.mem_image]
        exact ⟨(u, v), Finset.mem_filter.mpr ⟨hmemB, by rw [hval]; exact hnz⟩, rfl⟩
      have hmin := V.min'_le _ hmemV
      have hval' : val (u, v) = (u : ℝ) * Real.log p + (v : ℝ) * Real.log q := by rw [hval]
      rw [hval'] at hmin
      linarith
  · refine ⟨1, one_pos, ?_⟩
    intro u v hu hv hnz
    exfalso
    refine hne ⟨|val (u, v)|, ?_⟩
    rw [hV, Finset.mem_image]
    refine ⟨(u, v), Finset.mem_filter.mpr ⟨?_, by rw [hval]; exact hnz⟩, rfl⟩
    rw [hB, Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
    rw [abs_le] at hu hv
    exact ⟨⟨hu.1, hu.2⟩, ⟨hv.1, hv.2⟩⟩

/-- The mass of the bi-lattice train is `M²` bumps. -/
theorem autoCorr_biLatticeTrain_zero {a b w : ℝ} (hg : Continuous g) (hgc : HasCompactSupport g)
    (hw : 0 ≤ w) (hsupp : ∀ x, w < |x| → g x = 0) {M : ℕ}
    (hind : ∀ u v : ℤ, (u : ℝ) * a + (v : ℝ) * b = 0 → u = 0 ∧ v = 0)
    (hsep : ∀ u v : ℤ, |u| ≤ 2 * (M : ℤ) → |v| ≤ (M : ℤ) →
      ((u : ℝ) * a + (v : ℝ) * b ≠ 0) → 2 * w < |(u : ℝ) * a + (v : ℝ) * b|) :
    autoCorr (biLatticeTrain g a b M) 0 = ((M : ℝ) * (M : ℝ)) * autoCorr g 0 := by
  have h := autoCorr_biLatticeTrain_fst hg hgc hw hsupp (k := 0) (Nat.zero_le M) hind hsep
  rw [Nat.cast_zero, zero_mul] at h
  rw [h, Nat.sub_zero]

end GaloisForLFunctions.ArithmeticIncidencePositivity
