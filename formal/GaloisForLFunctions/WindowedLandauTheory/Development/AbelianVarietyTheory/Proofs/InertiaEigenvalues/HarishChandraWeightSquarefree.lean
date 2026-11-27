import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerMultiplicityOne
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotents
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraDegree

/-! The Whittaker weight of a squarefree polynomial label is the reciprocal
of the product of the cyclotomic order factors of its irreducible factors. -/

noncomputable section
open Polynomial WindowedLandauTheory.MainNotions.ArithmeticCylinders
open scoped Classical

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

private theorem normalized_cuspidal_degree (d : ℕ) (hd : 0 < d) :
    (∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1)) / primeToCharOrder g d =
      ((g : ℂ) ^ d - 1)⁻¹ := by
  let A : ℂ := ∏ i ∈ Finset.Ico 1 d, ((g : ℂ) ^ i - 1)
  have h : primeToCharOrder g d = A * ((g : ℂ) ^ d - 1) := by
    unfold primeToCharOrder A
    conv_lhs => rw [← Nat.sub_add_cancel hd, Finset.prod_range_succ, Nat.sub_add_cancel hd]
    rw [Finset.prod_Ico_eq_prod_range]
    exact congrArg (· * ((g : ℂ) ^ d - 1))
      (Finset.prod_congr rfl fun i _ => by rw [Nat.add_comm i 1])
  have hne := primeToCharOrder_ne_zero (g := g) d
  rw [h] at hne
  change A / primeToCharOrder g d = _
  rw [h, mul_comm A, div_mul_eq_div_div_swap, div_self (mul_ne_zero_iff.mp hne).1, one_div]

private theorem wh_rank_zero (ψ : AddChar (ZMod g) ℂ) :
    wh ψ (hcL ([] : List (Pc g)) 0) = 1 := by
  letI : Unique (Gn g 0) := ⟨⟨1⟩, fun x => Subsingleton.elim x 1⟩
  have hU (u : Gn g 0) : IsUniUp u.val := fun i => Fin.elim0 i
  simp [wh, eU, tr_eDat, hU, hcL_nil]

/-- A squarefree label has Whittaker series weight
`∏ (g^deg(P) - 1)⁻¹` over its distinct irreducible factors. -/
theorem wtC_eU_squarefree (L : LabelDatum g) (hg : 5 ≤ g) (ψ : AddChar (ZMod g) ℂ)
    (hψ : ψ ≠ 1) (f : (ZMod g)[X]) (hm : f.Monic) (hd : f.natDegree = n)
    (h0 : f.coeff 0 ≠ 0) (hs : Squarefree f) :
    wtC L (eU g n ψ) f =
      1 / ((UniqueFactorizationMonoid.normalizedFactors f).map
        (fun P => (g : ℝ) ^ P.natDegree - 1)).prod := by
  obtain ⟨Q, hQ, hQf, hQd, hser⟩ := squarefree_label_series L hg f hm hd h0 hs
  let χ := hcL (Q.map Prod.snd) n
  have hχ : IsIrr χ := by
    have hh : χ ∈ {η : Gn g n → ℂ | IsIrr η ∧ HasLabel L η f} := by
      rw [hser]
      exact Set.mem_singleton _
    exact hh.1
  have hcus (p : Pc g) (hp : p ∈ Q.map Prod.snd) : IsCusp p.2 := by
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact (hQ q hq).1.2.1
  have hwh : wh ψ χ = 1 := by
    by_cases hn : 0 < n
    · apply wh_eq_one_of_generic L hg hn ψ hψ hχ
      change wh ZMod.stdAddChar (hcL (Q.map Prod.snd) n) ≠ 0
      rw [← hQd]
      exact wh_hcL_ne_zero_of_cusp _ hcus
    · obtain rfl : n = 0 := by omega
      have hnil : Q = [] := by
        cases Q with
        | nil => rfl
        | cons p Q =>
          change p.2.1 + degL (Q.map Prod.snd) = 0 at hQd
          have hp := (hQ p List.mem_cons_self).1.2.1.1
          omega
      simpa only [χ, hnil, List.map_nil] using wh_rank_zero ψ
  have hrat : χ 1 / primeToCharOrder g n =
      (Q.map fun p => ((g : ℂ) ^ p.1.natDegree - 1)⁻¹).prod := by
    have h := hcL_one_normalized (Q.map Prod.snd)
    rw [hQd, List.map_map] at h
    refine h.trans (congrArg List.prod (List.map_congr_left fun p hp => ?_))
    have hp0 : 0 < p.2.1 := (hQ p hp).1.2.1.1
    rw [Function.comp_apply, (hQ p hp).2, normalized_cuspidal_degree p.2.1 hp0, (hQ p hp).1.1.2.2.2]
  let D : ℝ := ((UniqueFactorizationMonoid.normalizedFactors f).map
    (fun P => (g : ℝ) ^ P.natDegree - 1)).prod
  have hD : (Q.map fun p => ((g : ℂ) ^ p.1.natDegree - 1)⁻¹).prod = Complex.ofReal (D⁻¹) := by
    have hI (A : List ((ZMod g)[X] × Pc g)) :
        (A.map fun p => ((g : ℂ) ^ p.1.natDegree - 1)⁻¹).prod =
          ((A.map fun p => (g : ℂ) ^ p.1.natDegree - 1).prod)⁻¹ := by
      induction A with
      | nil => simp
      | cons p A ih => simp only [List.map_cons, List.prod_cons, mul_inv, ih]
    rw [hI, Complex.ofReal_inv]
    congr 1
    have hmap (A : List ((ZMod g)[X] × Pc g)) :
        (A.map fun p => (g : ℂ) ^ p.1.natDegree - 1).prod =
        Complex.ofReal (A.map fun p => (g : ℝ) ^ p.1.natDegree - 1).prod := by
      induction A with
      | nil => simp
      | cons p A ih => simp only [List.map_cons, List.prod_cons, Complex.ofReal_mul, ih,
          Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_one, Complex.ofReal_natCast]
    rw [hmap Q]
    congr 1
    unfold D
    rw [← hQf, Multiset.map_coe, Multiset.prod_coe, List.map_map]
    rfl
  have hsval : eSerC L n f = zOf χ := by
    unfold eSerC
    rw [hser, finsum_mem_singleton]
  have hU := (eU_mul_self_coeff_one (g := g) (n := n) ψ).2
  let q : ℝ := (g : ℝ) ^ (n * (n - 1) / 2)
  have hq : 0 < q := pow_pos (Nat.cast_pos.mpr (Fact.out : g.Prime).pos) _
  have hcast : Complex.ofReal q = (g : ℂ) ^ (n * (n - 1) / 2) := by simp [q]
  have hcoef : (eU g n ψ).coeff 1 = Complex.ofReal (q⁻¹) := by
    rw [hU, Complex.ofReal_inv, hcast]
  have hdeg : χ 1 / (Fintype.card (Gn g n) : ℂ) = Complex.ofReal (D⁻¹ * q⁻¹) := by
    rw [card_Gn_eq, ← hcast, div_mul_eq_div_div_swap, hrat, hD, Complex.ofReal_mul]
    simp only [Complex.ofReal_inv, div_eq_mul_inv]
  have htr : tr (eU g n ψ) χ = 1 := hwh
  rw [wtC, hsval, coeff_one_mul_zOf, htr, mul_one, hdeg, hcoef,
    Complex.ofReal_re, Complex.ofReal_re, one_div]
  exact (div_eq_iff (inv_ne_zero hq.ne')).2 rfl

end GlobalTheory.GLq
