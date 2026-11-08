import GaloisForLFunctions.CountingHolography.TheCountLawAtEveryGenus
import GaloisForLFunctions.RHTower.HyperellipticCharacterSums
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# The count law of every hyperelliptic curve

The corpus proves the Riemann hypothesis for `y² = f(x)` with `f` squarefree of **odd** degree
(`RHTower.Hyperelliptic.riemannHypothesis_oddHyperelliptic`). This module removes the parity, so the
count law holds on every hyperelliptic curve, in particular on every genus-two curve `y² = f(x)`,
`deg f ∈ {5, 6}`, whatever its Jacobian.

* **Norms of residues** (`algebraMap_resultant`): for monic `g`, `Res(g, r) = Π_{g(α)=0} r(α)` at
  every formal degree, so it only sees `r mod g` and is multiplicative.
* **A nonsquare norm** (`exists_nonsquare_unit`): for `g` squarefree of positive degree there is a
  unit `v mod g` with `χ(Res(g, v)) = −1`: at an irreducible factor `P`, `v = 1 + (g/P) w` with
  `v(α) = y₀` a nonsquare of `F[α]`, and `χ_F(N y₀) = χ_{F[α]}(y₀)`.
* **Vanishing at every degree** (`degSumW_eq_zero_of_squarefree`): the twist `h ↦ h − h mod g +
  v h mod g` permutes the monic polynomials of degree `k ≥ deg g` and multiplies `χ(Res(h, f))` by
  `−1`, so the L-function of `χ(Res(·, f))` is a polynomial of degree `< deg f`.
-/

open Polynomial Finset

noncomputable section

namespace GaloisForLFunctions.CountingHolography

open RHTower.Hyperelliptic RHTower.WeilKloosterman

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F]

/-! ### Resultants against a monic polynomial -/

section Norm

variable {g : F[X]}

/-- The product of `r` over the roots of `g` in an algebraic closure. -/
def rootProd (g r : F[X]) : AlgebraicClosure F :=
  ((g.map (algebraMap F (AlgebraicClosure F))).roots.map fun α => aeval α r).prod

/-- For monic `g`, `Res(g, r) = Π_{g(α) = 0} r(α)` at every formal degree `n ≥ deg r`. -/
theorem algebraMap_resultant (hg : g.Monic) (r : F[X]) {n : ℕ} (hn : r.natDegree ≤ n) :
    algebraMap F (AlgebraicClosure F) (resultant g r g.natDegree n) = rootProd g r := by
  rw [← resultant_map_map]
  have hdeg : (g.map (algebraMap F (AlgebraicClosure F))).natDegree = g.natDegree :=
    hg.natDegree_map _
  rw [← hdeg, resultant_eq_prod_eval _ _ n (natDegree_map_le.trans hn) (IsAlgClosed.splits _),
    (hg.map _).leadingCoeff, one_pow, one_mul, rootProd]
  congr 1
  exact Multiset.map_congr rfl fun α _ => by rw [eval_map_algebraMap]

/-- The resultant against a monic `g` does not depend on the formal degree. -/
theorem resultant_eq_of_le (hg : g.Monic) (r : F[X]) {n : ℕ} (hn : r.natDegree ≤ n) :
    resultant g r g.natDegree n = resultant g r := by
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [algebraMap_resultant hg r hn, algebraMap_resultant hg r le_rfl]

theorem rootProd_mul (g a b : F[X]) : rootProd g (a * b) = rootProd g a * rootProd g b := by
  simp [rootProd, Multiset.prod_map_mul]

theorem rootProd_modByMonic (hg : g.Monic) (r : F[X]) : rootProd g (r %ₘ g) = rootProd g r := by
  unfold rootProd
  congr 1
  refine Multiset.map_congr rfl fun α hα => ?_
  have hα0 : aeval α g = 0 := by
    rw [mem_roots (Polynomial.map_ne_zero hg.ne_zero), IsRoot, eval_map_algebraMap] at hα
    exact hα
  conv_rhs => rw [← modByMonic_add_div r g]
  simp [hα0]

/-- `Res(g, a b) = Res(g, a) Res(g, b)` for monic `g`. -/
theorem resultant_mul_monic (hg : g.Monic) (a b : F[X]) :
    resultant g (a * b) = resultant g a * resultant g b := by
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [map_mul, algebraMap_resultant hg _ le_rfl, algebraMap_resultant hg _ le_rfl,
    algebraMap_resultant hg _ le_rfl, rootProd_mul]

/-- `Res(g, r mod g) = Res(g, r)` for monic `g`. -/
theorem resultant_modByMonic (hg : g.Monic) (r : F[X]) : resultant g (r %ₘ g) = resultant g r := by
  apply (algebraMap F (AlgebraicClosure F)).injective
  rw [algebraMap_resultant hg _ le_rfl, algebraMap_resultant hg _ le_rfl, rootProd_modByMonic hg]

end Norm

/-! ### A unit with nonsquare norm -/

section Unit

variable [Fintype F] {g : F[X]}

/-- **A unit with nonsquare norm.** For `g` monic, squarefree, of positive degree, there are `v`, `a`
with `a v ≡ 1 mod g` and `χ(Res(g, v)) = −1`. -/
theorem exists_nonsquare_unit (hF : ringChar F ≠ 2) (hg : g.Monic) (hsq : Squarefree g)
    (hdeg : 0 < g.natDegree) :
    ∃ v a : F[X], AdjoinRoot.mk g a * AdjoinRoot.mk g v = 1 ∧
      quadraticChar F (resultant g v) = -1 := by
  -- a monic irreducible factor `P` and its cofactor `Q`
  obtain ⟨P₀, hP₀, hP₀g⟩ := WfDvdMonoid.exists_irreducible_factor
    (not_isUnit_of_natDegree_pos g hdeg) hg.ne_zero
  have hP₀0 : P₀ ≠ 0 := hP₀.ne_zero
  set P := P₀ * C P₀.leadingCoeff⁻¹
  have hPm : P.Monic := monic_mul_leadingCoeff_inv hP₀0
  have hPassoc : Associated P₀ P :=
    associated_mul_unit_right P₀ _ (isUnit_C.mpr (inv_ne_zero (leadingCoeff_ne_zero.mpr hP₀0)).isUnit)
  have hP : Irreducible P := hPassoc.irreducible hP₀
  have hPg : P ∣ g := hPassoc.symm.dvd.trans hP₀g
  set Q := g /ₘ P
  have hgPQ : g = P * Q := by
    have h := modByMonic_add_div g P
    rw [(modByMonic_eq_zero_iff_dvd hPm).mpr hPg, zero_add] at h
    exact h.symm
  -- the residue field `K = F[X]/(P)`
  haveI : Fact (Irreducible P) := ⟨hP⟩
  haveI : Module.Finite F (AdjoinRoot P) := (AdjoinRoot.powerBasis hPm.ne_zero).finite
  haveI : Finite (AdjoinRoot P) := Module.finite_of_finite F
  letI : Fintype (AdjoinRoot P) := Fintype.ofFinite _
  have hK : ringChar (AdjoinRoot P) ≠ 2 := by rwa [← Algebra.ringChar_eq F (AdjoinRoot P)]
  set x : AdjoinRoot P := AdjoinRoot.root P
  -- `Q(x) ≠ 0`, since `P² ∤ g`
  have hQx : aeval x Q ≠ 0 := by
    rw [AdjoinRoot.aeval_eq, Ne, AdjoinRoot.mk_eq_zero]
    intro hPQ
    have hPP : P * P ∣ g := hgPQ ▸ mul_dvd_mul_left P hPQ
    exact hP.not_isUnit (hsq P hPP)
  obtain ⟨y₀, hy₀⟩ := FiniteField.exists_nonsquare hK
  have hy₀0 : y₀ ≠ 0 := fun h => hy₀ (h ▸ ⟨0, by simp⟩)
  obtain ⟨w, hw⟩ := AdjoinRoot.mk_surjective (g := P) ((y₀ - 1) / aeval x Q)
  set v := 1 + Q * w
  have hvx : aeval x v = y₀ := by
    rw [map_add, map_one, map_mul, AdjoinRoot.aeval_eq w, hw]
    field_simp
    ring
  -- `Res(g, v) = Res(P, v)`: `v = 1` at the roots of `Q`
  have hres : resultant g v = resultant P v := by
    apply (algebraMap F (AlgebraicClosure F)).injective
    rw [algebraMap_resultant hg _ le_rfl, algebraMap_resultant hPm _ le_rfl]
    have hroots : (g.map (algebraMap F (AlgebraicClosure F))).roots =
        (P.map (algebraMap F (AlgebraicClosure F))).roots +
          (Q.map (algebraMap F (AlgebraicClosure F))).roots := by
      rw [hgPQ, Polynomial.map_mul, roots_mul]
      rw [← Polynomial.map_mul, ← hgPQ]
      exact Polynomial.map_ne_zero hg.ne_zero
    have hQ1 : ((Q.map (algebraMap F (AlgebraicClosure F))).roots.map fun α => aeval α v).prod = 1 := by
      refine Multiset.prod_eq_one fun z hz => ?_
      obtain ⟨β, hβ, rfl⟩ := Multiset.mem_map.mp hz
      have hQ0 : Q ≠ 0 := by
        rintro h
        rw [h, mul_zero] at hgPQ
        exact hg.ne_zero hgPQ
      rw [mem_roots (Polynomial.map_ne_zero hQ0), IsRoot, eval_map_algebraMap] at hβ
      simp [v, hβ]
    rw [rootProd, hroots, Multiset.map_add, Multiset.prod_add, hQ1, mul_one, rootProd]
  -- `Res(P, v) = N_{K/F}(v(x)) = N(y₀)`
  have hmin : minpoly F x = P := by
    rw [AdjoinRoot.minpoly_root hPm.ne_zero, hPm.leadingCoeff, inv_one, C_1, mul_one]
  have hfin : Module.finrank F (AdjoinRoot P) = P.natDegree := by
    rw [(AdjoinRoot.powerBasis hPm.ne_zero).finrank, AdjoinRoot.powerBasis_dim]
  have hnorm := norm_aeval_eq_resultant_pow (F := F) v x
  rw [hmin, hfin, Nat.div_self (hPm.natDegree_pos_of_not_isUnit hP.not_isUnit), pow_one, hvx] at hnorm
  -- `v` is a unit mod `g`
  have hcopP : IsCoprime v P := by
    refine ((Irreducible.coprime_iff_not_dvd hP).mpr ?_).symm
    intro hdvd
    rw [← AdjoinRoot.mk_eq_zero, ← AdjoinRoot.aeval_eq, hvx] at hdvd
    exact hy₀0 hdvd
  have hcopQ : IsCoprime v Q := ⟨1, -w, by ring⟩
  have hcop : IsCoprime v g := by
    rw [hgPQ]
    exact hcopP.mul_right hcopQ
  obtain ⟨a, b, hab⟩ := hcop
  refine ⟨v, a, ?_, ?_⟩
  · rw [← map_mul, show a * v = 1 - b * g by linear_combination hab, map_sub, map_one, map_mul,
      AdjoinRoot.mk_self, mul_zero, sub_zero]
  · rw [hres, ← hnorm, ← quadraticChar_norm hF y₀]
    exact quadraticChar_neg_one_iff_not_isSquare.mpr hy₀

end Unit

/-! ### Vanishing of the high degree sums -/

section Vanishing

variable {g : F[X]}

/-- The twist `T_v h = h − h mod g + v h mod g`, which multiplies the residue by `v`. -/
def twist (g v h : F[X]) : F[X] := h - h %ₘ g + (v * h) %ₘ g

theorem mk_twist (hg : g.Monic) (v h : F[X]) :
    AdjoinRoot.mk g (twist g v h) = AdjoinRoot.mk g (v * h) := by
  have e1 : AdjoinRoot.mk g (h %ₘ g) = AdjoinRoot.mk g h := by
    rw [← AdjoinRoot.modByMonicHom_mk hg, AdjoinRoot.mk_leftInverse hg]
  have e2 : AdjoinRoot.mk g ((v * h) %ₘ g) = AdjoinRoot.mk g (v * h) := by
    rw [← AdjoinRoot.modByMonicHom_mk hg, AdjoinRoot.mk_leftInverse hg]
  simp only [twist, map_add, map_sub, e1, e2, sub_self, zero_add]

theorem twist_modByMonic (hg : g.Monic) (v h : F[X]) : twist g v h %ₘ g = (v * h) %ₘ g := by
  rw [← AdjoinRoot.modByMonicHom_mk hg, mk_twist hg, AdjoinRoot.modByMonicHom_mk]

theorem twist_mem_monicDeg [Fintype F] (hg : g.Monic) {k : ℕ} (hk : g.natDegree ≤ k) (v : F[X]) {h : F[X]}
    (hh : h ∈ monicDeg (F := F) k) : twist g v h ∈ monicDeg (F := F) k := by
  obtain ⟨hmon, hdeg⟩ := mem_monicDeg.mp hh
  have hlt : (-(h %ₘ g) + (v * h) %ₘ g).degree < h.degree := by
    refine (degree_add_le _ _).trans_lt (max_lt ?_ ?_)
    · rw [degree_neg]
      refine (degree_modByMonic_lt h hg).trans_le ?_
      rw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hmon.ne_zero, hdeg]
      exact_mod_cast hk
    · refine (degree_modByMonic_lt _ hg).trans_le ?_
      rw [degree_eq_natDegree hg.ne_zero, degree_eq_natDegree hmon.ne_zero, hdeg]
      exact_mod_cast hk
  have e : twist g v h = h + (-(h %ₘ g) + (v * h) %ₘ g) := by unfold twist; ring
  rw [e]
  exact mem_monicDeg.mpr ⟨hmon.add_of_left hlt, by rw [natDegree_add_eq_left_of_degree_lt hlt, hdeg]⟩

/-- `T_a T_v = id` when `a v ≡ 1`. -/
theorem twist_twist (hg : g.Monic) {a v : F[X]} (hav : AdjoinRoot.mk g a * AdjoinRoot.mk g v = 1)
    (h : F[X]) : twist g a (twist g v h) = h := by
  have h1 : (a * twist g v h) %ₘ g = h %ₘ g := by
    rw [← AdjoinRoot.modByMonicHom_mk hg, (AdjoinRoot.mk g).map_mul, mk_twist hg,
      (AdjoinRoot.mk g).map_mul, ← mul_assoc, hav, one_mul, AdjoinRoot.modByMonicHom_mk]
  change twist g v h - twist g v h %ₘ g + (a * twist g v h) %ₘ g = h
  rw [twist_modByMonic hg, h1]
  unfold twist
  ring

/-- `Res(g, T_v h) = Res(g, v) Res(g, h)`. -/
theorem resultant_twist' (hg : g.Monic) (v h : F[X]) :
    resultant g (twist g v h) = resultant g v * resultant g h := by
  rw [← resultant_modByMonic hg, twist_modByMonic hg, resultant_modByMonic hg, resultant_mul_monic hg]

/-- The weight of `f` through its monic associate `g = f/lc`: on monic `h` of degree `k`,
`w_f(h) = χ(lc^k (−1)^{km}) χ(Res(g, h))`. -/
theorem hypW_eq_monic [Fintype F] {f : F[X]} (hf0 : f ≠ 0) {k : ℕ} {h : F[X]}
    (hh : h ∈ monicDeg (F := F) k) :
    hypW f h = chiC F (f.leadingCoeff ^ k * (-1) ^ (k * f.natDegree)) *
      chiC F (resultant (f * C f.leadingCoeff⁻¹) h) := by
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hgdeg : (f * C f.leadingCoeff⁻¹).natDegree = f.natDegree := natDegree_mul_C (inv_ne_zero hlc)
  have hfg : f = C f.leadingCoeff * (f * C f.leadingCoeff⁻¹) := by
    rw [mul_comm, mul_assoc, ← C_mul, inv_mul_cancel₀ hlc, C_1, mul_one]
  obtain ⟨-, hhdeg⟩ := mem_monicDeg.mp hh
  rw [hypW_eq_chiC, ← map_mul]
  congr 1
  conv_lhs => rw [hfg]
  rw [show (C f.leadingCoeff * (f * C f.leadingCoeff⁻¹)).natDegree = f.natDegree by rw [← hfg],
    resultant_C_mul_right, ← hgdeg, resultant_comm, hhdeg, hgdeg]
  ring

/-- **Vanishing at every degree.** For `f` squarefree of positive degree `m`, the degree sums
`s_k = Σ_{deg h = k} χ(Res(h, f))` vanish for `k ≥ m`. -/
theorem degSumW_eq_zero_of_squarefree [Fintype F] (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hdeg : 0 < f.natDegree) {k : ℕ} (hk : f.natDegree ≤ k) : degSumW (hypW f) k = 0 := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hdeg
  set m := f.natDegree
  set g := f * C f.leadingCoeff⁻¹
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  have hgm : g.Monic := monic_mul_leadingCoeff_inv hf0
  have hgdeg : g.natDegree = m := natDegree_mul_C (inv_ne_zero hlc)
  have hgsq : Squarefree g :=
    (associated_mul_unit_right f _ (isUnit_C.mpr (inv_ne_zero hlc).isUnit)).squarefree_iff.mp hsq
  unfold degSumW
  rw [Finset.sum_congr rfl fun h hh => hypW_eq_monic hf0 hh, ← Finset.mul_sum]
  refine mul_eq_zero_of_right _ ?_
  obtain ⟨v, a, hav, hv⟩ := exists_nonsquare_unit hF hgm hgsq (hgdeg ▸ hdeg)
  have hva : AdjoinRoot.mk g v * AdjoinRoot.mk g a = 1 := by rw [mul_comm]; exact hav
  have hkg : g.natDegree ≤ k := hgdeg ▸ hk
  set S := ∑ h ∈ monicDeg (F := F) k, chiC F (resultant g h)
  have hS : S = chiC F (resultant g v) * S := by
    calc S = ∑ h ∈ monicDeg (F := F) k, chiC F (resultant g (twist g v h)) := by
          refine Finset.sum_nbij' (twist g a) (twist g v) ?_ ?_ ?_ ?_ ?_
          · exact fun h hh => twist_mem_monicDeg hgm hkg a hh
          · exact fun h hh => twist_mem_monicDeg hgm hkg v hh
          · exact fun h _ => twist_twist hgm hva h
          · exact fun h _ => twist_twist hgm hav h
          · intro h _
            rw [twist_twist hgm hva]
      _ = chiC F (resultant g v) * S := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun h _ => ?_
          rw [resultant_twist' hgm, map_mul]
  rw [chiC_apply, hv] at hS
  have : (2 : ℂ) * S = 0 := by push_cast at hS; linear_combination hS
  simpa using this

end Vanishing

/-! ### The L-polynomial of every squarefree `f` -/

section LPoly

variable [Fintype F] {f : F[X]}

/-- **Vieta** for every squarefree `f`: `e_k(ω) = (−1)^k s_k`. -/
theorem esymm_lRoots_of_squarefree (hF : ringChar F ≠ 2) (hsq : Squarefree f)
    (hm : 0 < f.natDegree) (k : ℕ) : (lRoots f).esymm k = (-1) ^ k * degSum f k := by
  rcases Nat.lt_or_ge k f.natDegree with hk | hk
  · have h := coeff_eq_esymm_roots_of_card (p := lPoly f)
      (by rw [IsAlgClosed.card_roots_eq_natDegree]) (k := f.natDegree - 1 - k)
      (by rw [lPoly_natDegree f hm]; omega)
    rw [lPoly_coeff f (by omega), show f.natDegree - 1 - (f.natDegree - 1 - k) = k by omega,
      (lPoly_monic f hm).leadingCoeff, lPoly_natDegree f hm,
      show f.natDegree - 1 - (f.natDegree - 1 - k) = k by omega, one_mul] at h
    rw [h, ← mul_assoc, ← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow, one_mul]
    rfl
  · rw [show degSum f k = 0 from degSumW_eq_zero_of_squarefree hF hsq hm hk, mul_zero,
      Multiset.esymm, Multiset.powersetCard_eq_empty _ (by rw [card_lRoots f hm]; omega)]
    simp

/-- **Newton's identity for the reciprocal roots** of every squarefree `f`. -/
theorem newton_lRoots_of_squarefree (hF : ringChar F ≠ 2) (hsq : Squarefree f)
    (hm : 0 < f.natDegree) {n : ℕ} (hn : 0 < n) :
    (n : ℂ) * degSum f n = -∑ k ∈ range n, degSum f k * rootPowerSum f (n - k) := by
  have hN := GaloisForLFunctions.multiset_newton (rootEnum (lRoots f)) n hn
  have hmap : ∀ j, (univ.val.map fun i => rootEnum (lRoots f) i ^ j).sum = rootPowerSum f j := by
    intro j
    rw [show (univ.val.map fun i => rootEnum (lRoots f) i ^ j) =
        (univ.val.map (rootEnum (lRoots f))).map (· ^ j) by rw [Multiset.map_map]; rfl,
      univ_map_rootEnum]
    rfl
  simp only [hmap] at hN
  rw [univ_map_rootEnum] at hN
  simp only [esymm_lRoots_of_squarefree hF hsq hm] at hN
  have hanti : ∑ a ∈ {a ∈ antidiagonal n | a.1 ∈ Set.Ioo 0 n},
      (-1) ^ a.1 * ((-1) ^ a.1 * degSum f a.1) * rootPowerSum f a.2 =
      ∑ k ∈ range n, if 0 < k then degSum f k * rootPowerSum f (n - k) else 0 := by
    rw [Finset.sum_filter, Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => if a ∈ Set.Ioo 0 n then (-1) ^ a * ((-1) ^ a * degSum f a) * rootPowerSum f b
        else 0), sum_range_succ]
    simp only [Set.mem_Ioo, lt_irrefl, and_false, if_false, add_zero]
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkn := mem_range.mp hk
    by_cases hk0 : 0 < k
    · rw [if_pos ⟨hk0, hkn⟩, if_pos hk0, ← mul_assoc, ← pow_add, ← two_mul, pow_mul,
        neg_one_sq, one_pow, one_mul]
    · rw [if_neg (fun h => hk0 h.1), if_neg hk0]
  rw [hanti] at hN
  have hsplit0 : ∑ k ∈ range n, degSum f k * rootPowerSum f (n - k) =
      rootPowerSum f n + ∑ k ∈ range n, if 0 < k then degSum f k * rootPowerSum f (n - k) else 0 := by
    rw [← Nat.succ_pred_eq_of_pos hn, sum_range_succ', sum_range_succ']
    simp only [RHTower.Hyperelliptic.degSum_zero, one_mul, Nat.sub_zero, lt_irrefl, if_false, add_zero,
      Nat.succ_pos, if_true]
    ring
  rw [hsplit0]
  have hsign : (-1 : ℂ) ^ (n + 1) * n * ((-1) ^ n * degSum f n) = -(n * degSum f n) := by
    rw [pow_succ]
    have : ((-1 : ℂ) ^ n) * (-1) ^ n = 1 := by
      rw [← pow_add, ← two_mul, pow_mul, neg_one_sq, one_pow]
    linear_combination -(n * degSum f n) * this
  rw [hsign] at hN
  linear_combination hN

/-- **`c_n = −Σ ω_i^n`** for every squarefree `f`. -/
theorem powerSumW_eq_neg_rootPowerSum_of_squarefree (hF : ringChar F ≠ 2) (hsq : Squarefree f)
    (hm : 0 < f.natDegree) {n : ℕ} (hn : 0 < n) : powerSumW (hypW f) n = -rootPowerSum f n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    have hc := newton_identity (hypW f) (fun _ _ hP hQ => hypW_mul f hP hQ) (hypW_one f) (n' + 1)
    have hr := newton_lRoots_of_squarefree hF hsq hm hn
    change ((n' + 1 : ℕ) : ℂ) * degSum f (n' + 1) = _ at hc
    have hre : ∑ j ∈ Finset.Icc 1 (n' + 1), powerSumW (hypW f) j * degSumW (hypW f) (n' + 1 - j) =
        ∑ k ∈ range (n' + 1), powerSumW (hypW f) (n' + 1 - k) * degSum f k := by
      refine Finset.sum_nbij' (fun j => n' + 1 - j) (fun k => n' + 1 - k) ?_ ?_ ?_ ?_ ?_
      · intro j hj; rw [Finset.mem_Icc] at hj; rw [mem_range]; omega
      · intro k hk; rw [mem_range] at hk; rw [Finset.mem_Icc]; omega
      · intro j hj; rw [Finset.mem_Icc] at hj; omega
      · intro k hk; rw [mem_range] at hk; omega
      · intro j hj
        rw [Finset.mem_Icc] at hj
        rw [show n' + 1 - (n' + 1 - j) = j by omega]
        rfl
    rw [hre, sum_range_succ'] at hc
    rw [sum_range_succ'] at hr
    simp only [Nat.sub_zero, RHTower.Hyperelliptic.degSum_zero, mul_one, one_mul] at hc hr
    have hih : ∀ k ∈ range n', powerSumW (hypW f) (n' + 1 - (k + 1)) * degSum f (k + 1) =
        -(degSum f (k + 1) * rootPowerSum f (n' + 1 - (k + 1))) := by
      intro k hk
      have hk' := mem_range.mp hk
      rw [ih (n' + 1 - (k + 1)) (by omega) (by omega)]
      ring
    rw [Finset.sum_congr rfl hih, Finset.sum_neg_distrib] at hc
    linear_combination hr - hc

/-- **The character sum over every extension**: `Σ_{x ∈ E} χ_E(f(x)) = −Σ ω_i^{[E:F]}`. -/
theorem extHyp_eq_neg_sum_pow_of_squarefree (hF : ringChar F ≠ 2) (hsq : Squarefree f)
    (hm : 0 < f.natDegree) (E : Type*) [Field E] [Fintype E] [Algebra F E] :
    extHyp (E := E) f = -((lRoots f).map (· ^ Module.finrank F E)).sum := by
  rw [extHyp_eq_powerSumW hF f, powerSumW_eq_neg_rootPowerSum_of_squarefree hF hsq hm
    Module.finrank_pos, rootPowerSum]

end LPoly

/-! ### The trivial zero of an even-degree curve -/

section TrivialZero

variable [Fintype F] {g : F[X]}

/-- **The residue sum vanishes, and so does its monic part.** For `g` monic squarefree of even degree
`m > 0`, `Σ_{k < m} Σ_{deg h = k} χ(Res(g, h)) = 0`: the residues mod `g` are permuted by a unit of
nonsquare norm, and the nonzero residues are the `a h`, `a ≠ 0`, `h` monic of degree `< m`, with
`χ(Res(g, a h)) = χ(a^m) χ(Res(g, h)) = χ(Res(g, h))`. -/
theorem sum_monic_lt_resultant_eq_zero (hF : ringChar F ≠ 2) (hg : g.Monic) (hsq : Squarefree g)
    (hdeg : 0 < g.natDegree) (heven : Even g.natDegree) :
    ∑ k ∈ range g.natDegree, ∑ h ∈ monicDeg (F := F) k, chiC F (resultant g h) = 0 := by
  set m := g.natDegree
  haveI : Module.Finite F (AdjoinRoot g) := (AdjoinRoot.powerBasis' hg).finite
  haveI : Finite (AdjoinRoot g) := Module.finite_of_finite F
  letI : Fintype (AdjoinRoot g) := Fintype.ofFinite _
  set φ : AdjoinRoot g → ℂ := fun x => chiC F (resultant g (AdjoinRoot.modByMonicHom hg x))
  have hφmk : ∀ p, φ (AdjoinRoot.mk g p) = chiC F (resultant g p) := fun p => by
    simp only [φ, AdjoinRoot.modByMonicHom_mk, resultant_modByMonic hg]
  -- the full residue sum vanishes
  obtain ⟨v, a, hav, hv⟩ := exists_nonsquare_unit hF hg hsq hdeg
  have hfull : ∑ x, φ x = 0 := by
    set S := ∑ x, φ x
    have hu : IsUnit (AdjoinRoot.mk g v) := IsUnit.of_mul_eq_one_right (AdjoinRoot.mk g a) hav
    have hbij : Function.Bijective (AdjoinRoot.mk g v * ·) := IsUnit.isUnit_iff_mulLeft_bijective.mp hu
    have hS : S = chiC F (resultant g v) * S := by
      calc S = ∑ x, φ (AdjoinRoot.mk g v * x) :=
            (Fintype.sum_bijective _ hbij (fun x => φ (AdjoinRoot.mk g v * x)) φ fun _ => rfl).symm
        _ = chiC F (resultant g v) * S := by
            rw [Finset.mul_sum]
            refine Finset.sum_congr rfl fun x _ => ?_
            obtain ⟨p, rfl⟩ := AdjoinRoot.mk_surjective x
            rw [← map_mul, hφmk, hφmk, resultant_mul_monic hg, map_mul]
    rw [chiC_apply, hv] at hS
    have : (2 : ℂ) * S = 0 := by push_cast at hS; linear_combination hS
    simpa using this
  -- the nonzero residues are `a h`
  set U := (range m).biUnion fun k => monicDeg (F := F) k
  set D := (univ.filter fun a : F => a ≠ 0) ×ˢ U
  set Ψ : F × F[X] → AdjoinRoot g := fun p => AdjoinRoot.mk g (C p.1 * p.2)
  have hdegU : ∀ h ∈ U, h.Monic ∧ h.natDegree < m := by
    intro h hh
    obtain ⟨k, hk, hhk⟩ := Finset.mem_biUnion.mp hh
    obtain ⟨hmon, hd⟩ := mem_monicDeg.mp hhk
    exact ⟨hmon, hd ▸ mem_range.mp hk⟩
  have hred : ∀ p ∈ D, (C p.1 * p.2) %ₘ g = C p.1 * p.2 := by
    intro p hp
    obtain ⟨-, hpU⟩ := Finset.mem_product.mp hp
    obtain ⟨hmon, hlt⟩ := hdegU p.2 hpU
    refine (modByMonic_eq_self_iff hg).mpr ?_
    refine (degree_C_mul_le' _ _).trans_lt ?_
    rw [degree_eq_natDegree hmon.ne_zero, degree_eq_natDegree hg.ne_zero]
    exact_mod_cast hlt
  have hinj : Set.InjOn Ψ D := by
    intro p hp p' hp' he
    have h1 := congrArg (AdjoinRoot.modByMonicHom hg) he
    simp only [Ψ, AdjoinRoot.modByMonicHom_mk, hred p hp, hred p' hp'] at h1
    obtain ⟨hp1, hpU⟩ := Finset.mem_product.mp hp
    obtain ⟨hp1', hpU'⟩ := Finset.mem_product.mp hp'
    have ha0 : p.1 ≠ 0 := (Finset.mem_filter.mp hp1).2
    have hlc := congrArg leadingCoeff h1
    rw [leadingCoeff_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_C, (hdegU _ hpU).1.leadingCoeff,
      (hdegU _ hpU').1.leadingCoeff, mul_one, mul_one] at hlc
    rw [← hlc] at h1
    exact Prod.ext hlc (mul_left_cancel₀ (C_ne_zero.mpr ha0) h1)
  have himage : D.image Ψ = univ.erase 0 := by
    ext x
    simp only [Finset.mem_image, Finset.mem_erase, mem_univ, and_true]
    constructor
    · rintro ⟨p, hp, rfl⟩ h0
      have h1 := congrArg (AdjoinRoot.modByMonicHom hg) h0
      simp only [Ψ, AdjoinRoot.modByMonicHom_mk, hred p hp, map_zero] at h1
      obtain ⟨hp1, hpU⟩ := Finset.mem_product.mp hp
      have ha0 : p.1 ≠ 0 := (Finset.mem_filter.mp hp1).2
      exact mul_ne_zero (C_ne_zero.mpr ha0) (hdegU _ hpU).1.ne_zero h1
    · intro hx
      obtain ⟨p₀, rfl⟩ := AdjoinRoot.mk_surjective x
      have hmk : AdjoinRoot.mk g (p₀ %ₘ g) = AdjoinRoot.mk g p₀ := by
        rw [← AdjoinRoot.modByMonicHom_mk hg, AdjoinRoot.mk_leftInverse hg]
      set p := p₀ %ₘ g
      have hp0 : p ≠ 0 := fun h => hx (by rw [← hmk, h, map_zero])
      have hlc : p.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hp0
      have hplt : p.natDegree < m := by
        have := degree_modByMonic_lt p₀ hg
        rw [degree_eq_natDegree hp0, degree_eq_natDegree hg.ne_zero] at this
        exact_mod_cast this
      set h := C p.leadingCoeff⁻¹ * p
      have hmon : h.Monic := monic_C_mul_of_mul_leadingCoeff_eq_one (inv_mul_cancel₀ hlc)
      have hhdeg : h.natDegree = p.natDegree := natDegree_C_mul (inv_ne_zero hlc)
      refine ⟨(p.leadingCoeff, h), Finset.mem_product.mpr ⟨Finset.mem_filter.mpr ⟨mem_univ _, hlc⟩,
        Finset.mem_biUnion.mpr ⟨p.natDegree, mem_range.mpr hplt, mem_monicDeg.mpr ⟨hmon, hhdeg⟩⟩⟩, ?_⟩
      simp only [Ψ, h, ← mul_assoc, ← C_mul, mul_inv_cancel₀ hlc, C_1, one_mul, hmk]
  -- assemble
  have hφ0 : φ 0 = 0 := by
    have h0 : AdjoinRoot.modByMonicHom hg 0 = 0 := map_zero _
    change chiC F (resultant g (AdjoinRoot.modByMonicHom hg 0)) = 0
    rw [h0, ← resultant_eq_of_le hg 0 (n := 0) (by simp), resultant_zero_right, zero_pow hdeg.ne',
      zero_mul, MulChar.map_zero]
  have hsplit := Finset.add_sum_erase (univ : Finset (AdjoinRoot g)) φ (mem_univ 0)
  rw [hφ0, zero_add, ← himage, Finset.sum_image hinj, hfull] at hsplit
  -- `Σ_{(a, h)} χ(Res(g, a h)) = (q − 1) Σ_h χ(Res(g, h))`
  have hpair : ∀ p ∈ D, φ (Ψ p) = chiC F (resultant g p.2) := by
    intro p hp
    obtain ⟨hp1, -⟩ := Finset.mem_product.mp hp
    have ha0 : p.1 ≠ 0 := (Finset.mem_filter.mp hp1).2
    show φ (AdjoinRoot.mk g (C p.1 * p.2)) = _
    rw [hφmk, resultant_mul_monic hg, map_mul,
      ← resultant_eq_of_le hg (C p.1) (n := 0) (by simp), resultant_C_zero_right]
    obtain ⟨j, hj⟩ := heven
    rw [show p.1 ^ g.natDegree = (p.1 ^ j) ^ 2 by rw [← pow_mul]; congr 1; omega, chiC_apply,
      quadraticChar_sq_one' (pow_ne_zero _ ha0)]
    simp
  rw [Finset.sum_congr rfl hpair, Finset.sum_product] at hsplit
  simp only [Finset.sum_const, nsmul_eq_mul] at hsplit
  have hU : ∑ h ∈ U, chiC F (resultant g h) =
      ∑ k ∈ range m, ∑ h ∈ monicDeg (F := F) k, chiC F (resultant g h) := by
    refine Finset.sum_biUnion fun k _ k' _ hkk' => Finset.disjoint_left.mpr fun h hk hk' => ?_
    exact hkk' ((mem_monicDeg.mp hk).2.symm.trans (mem_monicDeg.mp hk').2)
  rw [hU] at hsplit
  have hq : ((univ.filter fun a : F => a ≠ 0).card : ℂ) ≠ 0 := by
    have : 0 < (univ.filter fun a : F => a ≠ 0).card :=
      Finset.card_pos.mpr ⟨1, Finset.mem_filter.mpr ⟨mem_univ _, one_ne_zero⟩⟩
    exact_mod_cast this.ne'
  exact (mul_eq_zero.mp hsplit).resolve_left hq

end TrivialZero

/-! ### The trivial reciprocal root -/

section TrivialRoot

variable [Fintype F] {f : F[X]}

theorem eval_lPoly (f : F[X]) (z : ℂ) :
    (lPoly f).eval z = ∑ k ∈ range f.natDegree, degSum f k * z ^ (f.natDegree - 1 - k) := by
  simp [lPoly, eval_finsetSum]

/-- **The trivial reciprocal root.** For `f` squarefree of even degree `m > 0`, `χ(lc f)` is a
reciprocal root of the L-function: `L(χ(lc f)) = Σ_{k<m} Σ_{deg h = k} χ(Res(f/lc, h)) = 0`. It is
the contribution of the two points at infinity. -/
theorem chiC_leadingCoeff_mem_lRoots (hF : ringChar F ≠ 2) (hsq : Squarefree f)
    (hm : 0 < f.natDegree) (heven : Even f.natDegree) : chiC F f.leadingCoeff ∈ lRoots f := by
  have hf0 : f ≠ 0 := by rintro rfl; simp at hm
  have hlc : f.leadingCoeff ≠ 0 := leadingCoeff_ne_zero.mpr hf0
  set m := f.natDegree
  set g := f * C f.leadingCoeff⁻¹
  have hgm : g.Monic := monic_mul_leadingCoeff_inv hf0
  have hgdeg : g.natDegree = m := natDegree_mul_C (inv_ne_zero hlc)
  have hgsq : Squarefree g :=
    (associated_mul_unit_right f _ (isUnit_C.mpr (inv_ne_zero hlc).isUnit)).squarefree_iff.mp hsq
  set ε := chiC F f.leadingCoeff
  have hε2 : ε * ε = 1 := by rw [← sq]; exact chiC_sq hlc
  -- `s_k(f) = ε^k Σ_{deg h = k} χ(Res(g, h))`
  have hs : ∀ k, degSum f k = ε ^ k * ∑ h ∈ monicDeg (F := F) k, chiC F (resultant g h) := by
    intro k
    unfold RHTower.Hyperelliptic.degSum degSumW
    rw [Finset.sum_congr rfl fun h hh => hypW_eq_monic hf0 hh, ← Finset.mul_sum, map_mul, map_pow,
      (heven.mul_left k).neg_one_pow, map_one, mul_one]
  have hT := sum_monic_lt_resultant_eq_zero hF hgm hgsq (hgdeg ▸ hm) (hgdeg ▸ heven)
  have hrange : range m = range g.natDegree := by rw [hgdeg]
  have heval : (lPoly f).eval ε = 0 := by
    rw [eval_lPoly]
    have hk : ∀ k ∈ range m, degSum f k * ε ^ (m - 1 - k) =
        ε ^ (m - 1) * ∑ h ∈ monicDeg (F := F) k, chiC F (resultant g h) := by
      intro k hk
      have hkm := mem_range.mp hk
      rw [hs k]
      have e : ε ^ k * ε ^ (m - 1 - k) = ε ^ (m - 1) * (ε ^ k * ε ^ k) := by
        rw [← pow_add, ← pow_add, ← pow_add]
        rw [show k + (m - 1 - k) = m - 1 by omega]
        rw [show m - 1 + (k + k) = (m - 1) + 2 * k by ring, pow_add, pow_mul, sq, hε2, one_pow, mul_one]
      rw [← mul_pow, hε2, one_pow, mul_one] at e
      linear_combination (∑ h ∈ monicDeg (F := F) k, chiC F (resultant g h)) * e
    rw [Finset.sum_congr rfl hk, ← Finset.mul_sum, hrange, hT, mul_zero]
  exact (mem_roots (lPoly_monic f hm).ne_zero).mpr heval

end TrivialRoot

/-! ### Even split curves through their odd model -/

section Split

variable {L : Type*} [Field L] [Fintype L]

/-- `χ_E(a) = χ_L(a)^{[E:L]}` for `a ∈ L`. -/
theorem chiC_algebraMap (hL : ringChar L ≠ 2) {E : Type*} [Field E] [Fintype E] [Algebra L E]
    (a : L) : chiC E (algebraMap L E a) = chiC L a ^ Module.finrank L E := by
  rw [chiC_apply, chiC_apply, quadraticChar_norm hL, Algebra.norm_algebraMap, map_pow]
  push_cast
  rfl

/-- **The even split curve through its odd model.** For `f = c Π_{s ∈ S} (X − s)` with `|S|` even and
`c₀ ∈ S`, moving `c₀` to infinity gives the odd model `G = Π_{s ≠ c₀} (X − (s − c₀)⁻¹)`; over every
extension `E` of degree `n`, `Σ_{x ∈ E} χ(f(x)) = −Σ_ω (ε ω)^n − χ(c)^n` with `ε = χ(c Π_{s ≠ c₀}(c₀ − s))`. -/
theorem extHyp_even_split (hL : ringChar L ≠ 2) {S : Finset L} {c₀ : L} (hc₀ : c₀ ∈ S)
    (heven : Even S.card) (c : L) (E : Type*) [Field E] [Fintype E] [Algebra L E] :
    extHyp (E := E) (C c * ∏ s ∈ S, (X - C s)) =
      -((lRoots (rootPoly ((S.erase c₀).image fun s => (s - c₀)⁻¹))).map fun ω =>
        (chiC L (c * ∏ s ∈ S.erase c₀, (c₀ - s)) * ω) ^ Module.finrank L E).sum -
      chiC L c ^ Module.finrank L E := by
  set n := Module.finrank L E
  set ι := algebraMap L E
  set T := (S.erase c₀).image fun s => (s - c₀)⁻¹
  set K := ∏ s ∈ S.erase c₀, (c₀ - s)
  set G0 := ∏ s ∈ S.erase c₀, (0 - (s - c₀)⁻¹)
  have hinj : Set.InjOn (fun s => (s - c₀)⁻¹) (S.erase c₀ : Set L) := by
    intro a _ b _ hab
    simpa using hab
  have hT : T.card = S.card - 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hc₀]
  have hTodd : Odd (rootPoly T).natDegree := by
    have : 1 ≤ S.card := Finset.card_pos.mpr ⟨c₀, hc₀⟩
    rw [natDegree_rootPoly, hT]
    rcases heven with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  -- `K G0 = 1`
  have hKG : K * G0 = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun s hs => ?_
    have hs0 : s - c₀ ≠ 0 := sub_ne_zero.mpr (Finset.ne_of_mem_erase hs)
    field_simp
    ring
  -- the corpus substitution over `E`
  set SE := S.map ⟨ι, ι.injective⟩
  have hsub := sum_quadraticChar_prod_eq_of_even (Finset.mem_map_of_mem ⟨ι, ι.injective⟩ hc₀)
    (show Even SE.card by rwa [Finset.card_map])
  rw [← Finset.map_erase] at hsub
  simp only [Finset.prod_map, Function.Embedding.coeFn_mk] at hsub
  have e1 : ∀ x : E, aeval x (C c * ∏ s ∈ S, (X - C s)) = ι c * ∏ s ∈ S, (x - ι s) := by
    intro x
    simp [ι, map_prod]
  have e2 : ∏ s ∈ S.erase c₀, (ι c₀ - ι s) = ι K := by simp [K, ι, map_prod]
  have e3 : ∀ u : E, ∏ s ∈ S.erase c₀, (u - (ι s - ι c₀)⁻¹) = aeval u (rootPoly T) := by
    intro u
    rw [rootPoly, map_prod, Finset.prod_image hinj]
    refine Finset.prod_congr rfl fun s _ => ?_
    simp [ι, map_sub, map_inv₀]
  have e4 : ∏ s ∈ S.erase c₀, (0 - (ι s - ι c₀)⁻¹) = ι G0 := by
    simp [G0, ι, map_prod, map_sub, map_inv₀]
  have e4' : aeval (0 : E) (rootPoly T) = ι G0 := (e3 0).symm.trans e4
  simp only [e2, e3, e4'] at hsub
  -- assemble
  have hext : extHyp (E := E) (C c * ∏ s ∈ S, (X - C s)) =
      chiC E (ι c) * ∑ x : E, chiC E (∏ s ∈ S, (x - ι s)) := by
    unfold extHyp
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [e1, ← chiC_apply, map_mul]
  have hG : ∑ u : E, chiC E (aeval u (rootPoly T)) = extHyp (E := E) (rootPoly T) := rfl
  simp only [← chiC_apply] at hsub
  rw [hext, hsub, hG, extHyp_eq_neg_sum_pow hL hTodd E, chiC_algebraMap hL, chiC_algebraMap hL,
    chiC_algebraMap hL]
  have hKG' : chiC L K ^ n * chiC L G0 ^ n = 1 := by rw [← mul_pow, ← map_mul, hKG, map_one, one_pow]
  have hmap : ((lRoots (rootPoly T)).map fun ω => (chiC L (c * K) * ω) ^ n).sum =
      (chiC L c ^ n * chiC L K ^ n) * ((lRoots (rootPoly T)).map (· ^ n)).sum := by
    rw [← Multiset.sum_map_mul_left]
    refine congrArg Multiset.sum (Multiset.map_congr rfl fun ω _ => ?_)
    rw [mul_pow, map_mul, mul_pow]
  rw [hmap]
  linear_combination (-(chiC L c ^ n)) * hKG'

end Split

/-! ### Descent: the Riemann hypothesis in even degree -/

section Descent

variable [Fintype F] {f : F[X]}

/-- **The Riemann hypothesis for even-degree hyperelliptic curves.** For `f` squarefree of even degree
`m ≥ 2`, the reciprocal roots are the trivial root `χ(lc f)` and `m − 2` roots of modulus `√q`. Over the
splitting field `L` the `[L : F]`-th powers are `χ_L(lc f)` and `ε` times the roots of the odd model. -/
theorem riemannHypothesis_evenHyperelliptic (hF : ringChar F ≠ 2) (hsq : Squarefree f)
    (hm : 2 ≤ f.natDegree) (heven : Even f.natDegree) :
    ∃ R : Multiset ℂ, lRoots f = chiC F f.leadingCoeff ::ₘ R ∧
      Multiset.card R = f.natDegree - 2 ∧ ∀ ω ∈ R, ‖ω‖ = Real.sqrt (Fintype.card F) := by
  have hm0 : 0 < f.natDegree := by omega
  set L := f.SplittingField
  set r := Module.finrank F L
  set fL := f.map (algebraMap F L)
  obtain ⟨hsqL, hsplitL, hdegL⟩ := map_splittingField hsq
  have hL : ringChar L ≠ 2 := by rwa [ringChar_splittingField]
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  haveI : CharP L (ringChar F) := charP_of_injective_algebraMap (algebraMap F L).injective _
  have hfL0 : fL ≠ 0 := by
    intro h
    have := congrArg natDegree h
    rw [hdegL, natDegree_zero] at this
    omega
  -- `fL = c Π_{s ∈ S} (X − s)`
  set S := rootSet' fL
  have hS : S.card = f.natDegree := by rw [card_rootSet' hsqL hsplitL, hdegL]
  set c := fL.leadingCoeff
  have hc0 : c ≠ 0 := leadingCoeff_ne_zero.mpr hfL0
  have hc : c = algebraMap F L f.leadingCoeff := by simp [c, fL, leadingCoeff_map]
  have hfL : fL = C c * ∏ s ∈ S, (X - C s) := by
    have h := C_leadingCoeff_mul_prod_multiset_X_sub_C (p := fL) (splits_iff_card_roots.mp hsplitL)
    rw [prod_roots_eq_prod_rootSet' hsqL] at h
    exact h.symm
  obtain ⟨c₀, hc₀⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  have hSeven : Even S.card := hS ▸ heven
  set T := (S.erase c₀).image fun s => (s - c₀)⁻¹
  set K := ∏ s ∈ S.erase c₀, (c₀ - s)
  set ε := chiC L (c * K)
  have hK0 : K ≠ 0 := Finset.prod_ne_zero_iff.mpr fun s hs =>
    sub_ne_zero.mpr (Finset.ne_of_mem_erase hs).symm
  have hinj : Set.InjOn (fun s => (s - c₀)⁻¹) (S.erase c₀ : Set L) :=
    fun a _ b _ hab => sub_left_injective (inv_injective hab)
  have hT : T.card = f.natDegree - 1 := by
    rw [Finset.card_image_of_injOn hinj, Finset.card_erase_of_mem hc₀, hS]
  have hTodd : Odd (rootPoly T).natDegree := by
    rw [natDegree_rootPoly, hT]
    rcases heven with ⟨k, hk⟩
    exact ⟨k - 1, by omega⟩
  obtain ⟨hcardG, hnormG, -⟩ :=
    riemannHypothesis_oddHyperelliptic.{_, 0} hL (squarefree_rootPoly T) hTodd
  rw [natDegree_rootPoly, hT] at hcardG
  -- descent: `(lRoots f)^r = χ_L(c) :: ε · lRoots G`
  have hdesc : (lRoots f).map (· ^ r) = chiC L c ::ₘ (lRoots (rootPoly T)).map (ε * ·) := by
    refine GaloisForLFunctions.multiset_eq_of_powerSum_eq fun n => ?_
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp only [pow_zero, Multiset.map_const', Multiset.sum_replicate, Multiset.card_map,
        Multiset.card_cons, card_lRoots f hm0, hcardG]
      congr 1
      omega
    haveI : NeZero n := ⟨hn.ne'⟩
    let E := FiniteField.Extension L (ringChar F) n
    letI : Fintype E := Fintype.ofFinite E
    letI : Algebra F E := ((algebraMap L E).comp (algebraMap F L)).toAlgebra
    haveI : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun _ => rfl
    have hfin : Module.finrank F E = r * n := by
      rw [← Module.finrank_mul_finrank F L E, FiniteField.finrank_extension]
    have hsame : extHyp (F := F) (E := E) f = extHyp (F := L) (E := E) fL := by
      unfold extHyp
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [aeval_map_algebraMap]
    have hF' := extHyp_eq_neg_sum_pow_of_squarefree hF hsq hm0 E
    have hL' := extHyp_even_split hL hc₀ hSeven c E
    rw [← hfL, FiniteField.finrank_extension] at hL'
    rw [hsame, hL', hfin] at hF'
    have e : ((lRoots f).map (· ^ r)).map (· ^ n) = (lRoots f).map (· ^ (r * n)) := by
      rw [Multiset.map_map]
      exact Multiset.map_congr rfl fun ω _ => by simp [← pow_mul]
    rw [e, Multiset.map_cons, Multiset.sum_cons, Multiset.map_map]
    simp only [Function.comp_def]
    linear_combination hF'
  -- the trivial root and the rest
  have htriv := chiC_leadingCoeff_mem_lRoots hF hsq hm0 heven
  set R := (lRoots f).erase (chiC F f.leadingCoeff)
  have hR : lRoots f = chiC F f.leadingCoeff ::ₘ R := (Multiset.cons_erase htriv).symm
  have hcl : chiC L c = chiC F f.leadingCoeff ^ r := by rw [hc, chiC_algebraMap hF]
  rw [hR, Multiset.map_cons, hcl, Multiset.cons_inj_right] at hdesc
  refine ⟨R, hR, ?_, ?_⟩
  · have := card_lRoots f hm0
    rw [hR, Multiset.card_cons] at this
    omega
  · intro ω hω
    have hmem : ω ^ r ∈ (lRoots (rootPoly T)).map (ε * ·) := hdesc ▸ Multiset.mem_map_of_mem _ hω
    obtain ⟨ω', hω', he⟩ := Multiset.mem_map.mp hmem
    have hε : ‖ε‖ = 1 := norm_chiC (mul_ne_zero hc0 hK0)
    have h := hnormG ω' hω'
    have hr : 0 < r := Module.finrank_pos
    have hcardL : (Fintype.card L : ℝ) = (Fintype.card F : ℝ) ^ r := by
      rw [Module.card_eq_pow_finrank (K := F) (V := L)]
      push_cast
      rfl
    have hpow : Real.sqrt ((Fintype.card F : ℝ) ^ r) = Real.sqrt (Fintype.card F) ^ r := by
      rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), ← pow_mul, mul_comm, pow_mul,
        Real.sq_sqrt (Nat.cast_nonneg _)]
    have hnr : ‖ω‖ ^ r = Real.sqrt (Fintype.card F) ^ r := by
      rw [← norm_pow, ← he, norm_mul, hε, one_mul, h, hcardL, hpow]
    exact (pow_left_inj₀ (norm_nonneg ω) (Real.sqrt_nonneg _) hr.ne').mp hnr

/-- **The Hasse–Weil bound in even degree.** For `y² = f(x)`, `f` squarefree of even degree `m ≥ 2`,
over every finite extension `E`: the smooth model has the affine points and `1 + χ_E(lc f)` points at
infinity, and `|#{y² = f(x)}(E) + χ_E(lc f) − |E|| ≤ (m − 2) √|E|`. -/
theorem abs_card_points_sub_le_evenHyperelliptic (hF : ringChar F ≠ 2) (hsq : Squarefree f)
    (hm : 2 ≤ f.natDegree) (heven : Even f.natDegree) (E : Type*) [Field E] [Fintype E]
    [Algebra F E] :
    |((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℝ) +
        (quadraticChar E (algebraMap F E f.leadingCoeff) : ℝ) - Fintype.card E| ≤
      (f.natDegree - 2 : ℕ) * Real.sqrt (Fintype.card E) := by
  have hm0 : 0 < f.natDegree := by omega
  obtain ⟨R, hR, hcardR, hnormR⟩ := riemannHypothesis_evenHyperelliptic hF hsq hm heven
  have hE : ringChar E ≠ 2 := by rwa [← Algebra.ringChar_eq F E]
  set n := Module.finrank F E
  have hcardE : Fintype.card E = Fintype.card F ^ n := Module.card_eq_pow_finrank
  have hcount := card_points_eq hE (f.map (algebraMap F E))
  simp only [eval_map, ← aeval_def] at hcount
  have hsum := extHyp_eq_neg_sum_pow_of_squarefree hF hsq hm0 E
  rw [hR, Multiset.map_cons, Multiset.sum_cons] at hsum
  have hχ : chiC E (algebraMap F E f.leadingCoeff) = chiC F f.leadingCoeff ^ n := chiC_algebraMap hF _
  -- the real quantity is `−Σ_R ω^n`
  have hkey : ((((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℝ) +
      (quadraticChar E (algebraMap F E f.leadingCoeff) : ℝ) - Fintype.card E : ℝ) : ℂ) =
      -(R.map (· ^ n)).sum := by
    have h1 : (((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℤ) : ℂ) =
        extHyp (E := E) f + Fintype.card E := by
      rw [hcount]
      unfold extHyp
      push_cast
      rfl
    push_cast
    rw [← chiC_apply, hχ]
    have h1' : (((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℕ) : ℂ) =
        extHyp (E := E) f + Fintype.card E := by exact_mod_cast h1
    rw [h1', hsum]
    ring
  rw [← Real.norm_eq_abs, ← Complex.norm_real, hkey, norm_neg]
  calc ‖(R.map (· ^ n)).sum‖ ≤ (R.map (fun ω => ‖ω ^ n‖)).sum := by
        simpa [Multiset.map_map] using norm_multiset_sum_le (R.map (· ^ n))
    _ = (R.map (fun _ => Real.sqrt (Fintype.card F) ^ n)).sum := by
        congr 1
        exact Multiset.map_congr rfl fun ω hω => by rw [norm_pow, hnormR ω hω]
    _ = (f.natDegree - 2 : ℕ) * Real.sqrt (Fintype.card E) := by
        rw [Multiset.map_const', Multiset.sum_replicate, hcardR, nsmul_eq_mul, hcardE, Nat.cast_pow]
        congr 1
        rw [eq_comm, Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), ← pow_mul, mul_comm,
          pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

end Descent

/-! ### The count law of every hyperelliptic curve -/

section CountLaw

variable [Fintype F] {f : F[X]}

/-- The points at infinity of the smooth model of `y² = f(x)` over `E`: one in odd degree,
`1 + χ_E(lc f)` in even degree. -/
def pointsAtInfinity (f : F[X]) (E : Type*) [Field E] [Fintype E] [Algebra F E] : ℤ :=
  if Odd f.natDegree then 1 else 1 + quadraticChar E (algebraMap F E f.leadingCoeff)

/-- **Hasse–Weil for every hyperelliptic curve.** For `f` squarefree of degree `2g + 1` or `2g + 2`
and every finite extension `E`, `|N_E − |E| − 1| ≤ 2g √|E|`, where `N_E` counts the affine points and
the points at infinity. -/
theorem abs_card_points_sub_le_hyperelliptic (hF : ringChar F ≠ 2) (hsq : Squarefree f) {g : ℕ}
    (hdeg : f.natDegree = 2 * g + 1 ∨ f.natDegree = 2 * g + 2) (E : Type*) [Field E] [Fintype E]
    [Algebra F E] :
    |((((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℤ) + pointsAtInfinity f E : ℤ) : ℝ) -
        Fintype.card E - 1| ≤ 2 * g * Real.sqrt (Fintype.card E) := by
  rcases hdeg with h | h
  · have hodd : Odd f.natDegree := ⟨g, h⟩
    have hb := abs_card_points_sub_le_oddHyperelliptic hF hsq hodd E
    rw [h, show 2 * g + 1 - 1 = 2 * g by omega] at hb
    simp only [pointsAtInfinity, if_pos hodd]
    push_cast at hb ⊢
    convert hb using 2
    ring
  · have heven : Even f.natDegree := ⟨g + 1, by omega⟩
    have hnodd : ¬ Odd f.natDegree := Nat.not_odd_iff_even.mpr heven
    have hb := abs_card_points_sub_le_evenHyperelliptic hF hsq (by omega) heven E
    rw [h, show 2 * g + 2 - 2 = 2 * g by omega] at hb
    simp only [pointsAtInfinity, if_neg hnodd]
    push_cast at hb ⊢
    convert hb using 2
    ring

/-- **The count law of every hyperelliptic curve, at every level.** For `f` squarefree of degree
`2g + 1` or `2g + 2`, `g ≥ 1`, odd characteristic, and every finite extension `E`, the channel
numbers `g`, `g |E|`, `N_E + (g − 1)(|E| + 1)` extend to a count law, `N_E` the number of points of the
smooth model. -/
theorem hyperelliptic_countLaw_every (hF : ringChar F ≠ 2) (hsq : Squarefree f) {g : ℕ}
    (hg : 1 ≤ g) (hdeg : f.natDegree = 2 * g + 1 ∨ f.natDegree = 2 * g + 2) (E : Type*) [Field E]
    [Fintype E] [Algebra F E] :
    ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ (K 0 1 : ℤ) = g ∧ (K 1 0 : ℤ) = g * Fintype.card E ∧
      (K 1 1 : ℤ) = (((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℤ) +
        pointsAtInfinity f E) + (g - 1) * (Fintype.card E + 1) := by
  set N : ℤ := ((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℤ) + pointsAtInfinity f E
  set Q : ℤ := Fintype.card E
  have hb := abs_card_points_sub_le_hyperelliptic hF hsq hdeg E
  -- `(Q + 1 − N)² ≤ 4g²Q`
  have ha : (Q + 1 - N) ^ 2 ≤ 4 * (g : ℤ) ^ 2 * Q := by
    have hQ : (0 : ℝ) ≤ Q := by simp [Q]
    have hsq' : Real.sqrt (Q : ℝ) ^ 2 = Q := Real.sq_sqrt hQ
    have h1 : |((Q + 1 - N : ℤ) : ℝ)| ≤ 2 * g * Real.sqrt Q := by
      rw [show ((Q + 1 - N : ℤ) : ℝ) = -((N : ℝ) - Q - 1) by push_cast; ring, abs_neg]
      exact_mod_cast hb
    have h2 : ((Q + 1 - N : ℤ) : ℝ) ^ 2 ≤ (2 * g * Real.sqrt Q) ^ 2 := by
      rw [← sq_abs]
      exact pow_le_pow_left₀ (abs_nonneg _) h1 2
    rw [mul_pow, mul_pow, hsq'] at h2
    have : ((Q + 1 - N : ℤ) : ℝ) ^ 2 ≤ ((4 * (g : ℤ) ^ 2 * Q : ℤ) : ℝ) := by
      push_cast at h2 ⊢
      linarith
    exact_mod_cast this
  obtain ⟨K, hK, h01, h10, h11⟩ :=
    (exists_genusCountLaw_iff (g := (g : ℤ)) (Q := Q) (a := Q + 1 - N) (by exact_mod_cast hg)).mpr ha
  exact ⟨K, hK, h01, h10, by rw [h11]; ring⟩

/-- **The count law of every genus-two curve.** Every curve `y² = f(x)` of genus two over a finite
field of odd characteristic, `f` squarefree of degree `5` or `6`, whatever its Jacobian, has the count
law at every level: channel numbers `2`, `2|E|`, `N_E + |E| + 1`. -/
theorem genusTwo_countLaw (hF : ringChar F ≠ 2) (hsq : Squarefree f)
    (hdeg : f.natDegree = 5 ∨ f.natDegree = 6) (E : Type*) [Field E] [Fintype E] [Algebra F E] :
    ∃ K : ℤ → ℤ → ℕ, CountLaw K ∧ (K 0 1 : ℤ) = 2 ∧ (K 1 0 : ℤ) = 2 * Fintype.card E ∧
      (K 1 1 : ℤ) = (((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℤ) +
        pointsAtInfinity f E) + (Fintype.card E + 1) := by
  obtain ⟨K, hK, h01, h10, h11⟩ := hyperelliptic_countLaw_every hF hsq (g := 2) (by norm_num)
    (by omega) E
  exact ⟨K, hK, by rw [h01]; norm_num, by rw [h10]; norm_num, by rw [h11]; ring⟩

end CountLaw

end GaloisForLFunctions.CountingHolography

end
