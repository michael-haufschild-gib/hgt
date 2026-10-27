import GaloisForLFunctions.RHTower.HyperellipticRiemannHypothesis
import GaloisForLFunctions.HTGeometry.MultisetNewtonSolve

/-!
# The Riemann hypothesis for odd-degree hyperelliptic curves, by descent

Let `F` be finite of odd characteristic, `q = |F|`, and `f ∈ F[X]` squarefree of odd degree `m`;
let `ω` be the `m − 1` reciprocal roots of the L-function of `w(P) = χ(Res(P, f))`. Over the
splitting field `L` of `f`, `[L : F] = r`, the split case gives reciprocal roots `ω'` of modulus
`√|L| = q^{r/2}`. Every extension `E` of `L` of degree `n` is an extension of `F` of degree `rn`,
and `Σ_{x∈E} χ_E(f(x))` is the same sum for both, so `Σ_i (ω_i^r)^n = Σ_j ω'^n_j` for all `n`.
Power sums determine a multiset, hence `{ω_i^r} = {ω'_j}` (`map_pow_lRoots_eq`) and `|ω_i| = √q`
(`riemannHypothesis_oddHyperelliptic`), with the Hasse–Weil bound over every extension
(`abs_card_points_sub_le_oddHyperelliptic`).
-/

open Polynomial Finset

namespace GaloisForLFunctions.RHTower.Hyperelliptic

open WeilKloosterman

attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- The splitting field of `f`, as a finite field. -/
noncomputable instance (f : F[X]) : Fintype f.SplittingField := Fintype.ofFinite _

omit [Fintype F] in
theorem ringChar_splittingField (f : F[X]) : ringChar f.SplittingField = ringChar F :=
  (Algebra.ringChar_eq F f.SplittingField).symm

/-- Over the splitting field the curve is split, squarefree, of the same degree. -/
theorem map_splittingField {f : F[X]} (hsq : Squarefree f) :
    Squarefree (f.map (algebraMap F f.SplittingField)) ∧
      (f.map (algebraMap F f.SplittingField)).Splits ∧
      (f.map (algebraMap F f.SplittingField)).natDegree = f.natDegree :=
  ⟨((PerfectField.separable_iff_squarefree.mpr hsq).map).squarefree, SplittingField.splits f,
    natDegree_map _⟩

/-- **Base change of the reciprocal roots**: the reciprocal roots over the splitting field `L`
are the `[L : F]`-th powers of those over `F`. -/
theorem map_pow_lRoots_eq (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hodd : Odd f.natDegree) :
    (lRoots f).map (· ^ Module.finrank F f.SplittingField) =
      lRoots (f.map (algebraMap F f.SplittingField)) := by
  set L := f.SplittingField
  set g := f.map (algebraMap F L)
  set r := Module.finrank F L
  obtain ⟨hsqg, hsplitg, hdegg⟩ := map_splittingField hsq
  have hL : ringChar L ≠ 2 := by rwa [ringChar_splittingField]
  have hoddg : Odd g.natDegree := hdegg ▸ hodd
  haveI : Fact (ringChar F).Prime := ⟨CharP.char_is_prime F _⟩
  haveI : CharP L (ringChar F) := charP_of_injective_algebraMap (algebraMap F L).injective _
  refine GaloisForLFunctions.multiset_eq_of_powerSum_eq fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have hdegg' : g.natDegree = f.natDegree := hdegg
    simp only [pow_zero, Multiset.map_const', Multiset.sum_replicate, Multiset.card_map,
      card_lRoots f hodd.pos, card_lRoots g hoddg.pos, hdegg']
  -- the extension of `L` of degree `n` is an extension of `F` of degree `rn`
  haveI : NeZero n := ⟨hn.ne'⟩
  let E := FiniteField.Extension L (ringChar F) n
  letI : Fintype E := Fintype.ofFinite E
  letI : Algebra F E := ((algebraMap L E).comp (algebraMap F L)).toAlgebra
  haveI : IsScalarTower F L E := IsScalarTower.of_algebraMap_eq fun _ => rfl
  have hfin : Module.finrank F E = r * n := by
    rw [← Module.finrank_mul_finrank F L E, FiniteField.finrank_extension]
  have hsame : extHyp (F := F) (E := E) f = extHyp (F := L) (E := E) g := by
    unfold extHyp
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [aeval_map_algebraMap]
  have hF' := extHyp_eq_neg_sum_pow hF hodd E
  have hL' := (riemannHypothesis_splitHyperelliptic hL hsqg hsplitg hoddg).2.2 E
  rw [hsame, hL', hfin, FiniteField.finrank_extension, neg_inj] at hF'
  rw [Multiset.map_map, hF']
  congr 1
  exact Multiset.map_congr rfl fun ω _ => by simp [← pow_mul]

/-- **The Riemann hypothesis for odd-degree hyperelliptic curves over finite fields.** For `F`
finite of odd characteristic, `q = |F|`, and `f ∈ F[X]` squarefree of odd degree `m`, the `m − 1`
reciprocal roots of the L-function have modulus `√q`, and for every finite extension `E` of degree
`n`, `Σ_{x ∈ E} χ_E(f(x)) = −Σ_i ω_i^n`. -/
theorem riemannHypothesis_oddHyperelliptic (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hodd : Odd f.natDegree) :
    Multiset.card (lRoots f) = f.natDegree - 1 ∧
      (∀ ω ∈ lRoots f, ‖ω‖ = Real.sqrt (Fintype.card F)) ∧
      ∀ (E : Type*) [Field E] [Fintype E] [Algebra F E],
        extHyp (E := E) f = -((lRoots f).map (· ^ Module.finrank F E)).sum := by
  refine ⟨card_lRoots f hodd.pos, ?_, fun E _ _ _ => extHyp_eq_neg_sum_pow hF hodd E⟩
  set L := f.SplittingField
  set r := Module.finrank F L
  obtain ⟨hsqg, hsplitg, hdegg⟩ := map_splittingField hsq
  have hL : ringChar L ≠ 2 := by rwa [ringChar_splittingField]
  have hnormL := (riemannHypothesis_splitHyperelliptic.{_, 0} hL hsqg hsplitg (hdegg ▸ hodd)).2.1
  have hr : 0 < r := Module.finrank_pos
  have hcardL : (Fintype.card L : ℝ) = (Fintype.card F : ℝ) ^ r := by
    rw [Module.card_eq_pow_finrank (K := F) (V := L)]; push_cast; rfl
  intro ω hω
  have hmem : ω ^ r ∈ lRoots (f.map (algebraMap F L)) := by
    rw [← map_pow_lRoots_eq hF hsq hodd]; exact Multiset.mem_map_of_mem _ hω
  have h := hnormL _ hmem
  have hpow : Real.sqrt ((Fintype.card F : ℝ) ^ r) = Real.sqrt (Fintype.card F) ^ r := by
    rw [Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), ← pow_mul, mul_comm, pow_mul,
      Real.sq_sqrt (Nat.cast_nonneg _)]
  rw [norm_pow, hcardL, hpow] at h
  exact (pow_left_inj₀ (norm_nonneg ω) (Real.sqrt_nonneg _) hr.ne').mp h

/-- **The Hasse–Weil bound** for `y² = f(x)`, `f` squarefree of odd degree `m`, over every finite
extension `E` of `F`: `|#{(x, y) ∈ E² : y² = f(x)} − |E|| ≤ (m − 1) √|E|`. -/
theorem abs_card_points_sub_le_oddHyperelliptic (hF : ringChar F ≠ 2) {f : F[X]}
    (hsq : Squarefree f) (hodd : Odd f.natDegree) (E : Type*) [Field E] [Fintype E]
    [Algebra F E] :
    |((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℝ) - Fintype.card E| ≤
      (f.natDegree - 1 : ℕ) * Real.sqrt (Fintype.card E) := by
  obtain ⟨hcardω, hnorm, hsum⟩ := riemannHypothesis_oddHyperelliptic hF hsq hodd
  have hE : ringChar E ≠ 2 := by rwa [← Algebra.ringChar_eq F E]
  set n := Module.finrank F E
  have hcardE : Fintype.card E = Fintype.card F ^ n := Module.card_eq_pow_finrank
  have hcount := card_points_eq hE (f.map (algebraMap F E))
  simp only [eval_map, ← aeval_def] at hcount
  have hR : ((univ.filter fun q : E × E => q.2 ^ 2 = aeval q.1 f).card : ℝ) - Fintype.card E =
      ((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hcount
    push_cast at this ⊢
    linarith
  rw [hR]
  have hC : ‖((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ)‖ =
      |((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℝ)| := by
    rw [show (((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ)) =
      (((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℝ) : ℂ) by push_cast; rfl,
      Complex.norm_real, Real.norm_eq_abs]
  rw [← hC]
  have hext : ((∑ x : E, quadraticChar E (aeval x f) : ℤ) : ℂ) = extHyp (E := E) f := by
    unfold extHyp; push_cast; rfl
  rw [hext, hsum E, norm_neg]
  calc ‖((lRoots f).map (· ^ n)).sum‖ ≤ ((lRoots f).map (fun ω => ‖ω ^ n‖)).sum := by
        simpa [Multiset.map_map] using norm_multiset_sum_le ((lRoots f).map (· ^ n))
    _ = ((lRoots f).map (fun _ => Real.sqrt (Fintype.card F) ^ n)).sum := by
        congr 1
        exact Multiset.map_congr rfl fun ω hω => by rw [norm_pow, hnorm ω hω]
    _ = (f.natDegree - 1 : ℕ) * Real.sqrt (Fintype.card E) := by
        rw [Multiset.map_const', Multiset.sum_replicate, hcardω, nsmul_eq_mul, hcardE,
          Nat.cast_pow]
        congr 1
        rw [eq_comm, Real.sqrt_eq_iff_eq_sq (by positivity) (by positivity), ← pow_mul, mul_comm,
          pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]

end GaloisForLFunctions.RHTower.Hyperelliptic
