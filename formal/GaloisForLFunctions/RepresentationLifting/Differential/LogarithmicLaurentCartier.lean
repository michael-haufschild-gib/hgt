import GaloisForLFunctions.RepresentationLifting.Differential.LogarithmicPCurvature
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.LinearAlgebra.Eigenspace.Minpoly
import Mathlib.LinearAlgebra.Finsupp.LSum
import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# Laurent Cartier descent for constant residues

Prime-field Lagrange projectors split every residue satisfying N^p = N,
even on infinite-dimensional modules. Integral shifts of those eigenspaces
construct a Laurent-linear gauge from Euler to Euler minus N. Conversely,
gauge equivalence forces zero p-curvature. Horizontal sections are explicit
Frobenius dilations with the residue component placed in its congruence class.

This extends the exponent-class decomposition in Fersi, arXiv:2611.20395,
Section 4.4, to all p-flat constant-residue Laurent connections.
-/

noncomputable section
open Polynomial
open scoped BigOperators
namespace GaloisForLFunctions.RepresentationLifting.DividedPower
variable (p : ℕ) [Fact p.Prime] {W : Type*} [AddCommGroup W] [Module (ZMod p) W]

private theorem prime_basis_eq_indicator (a : ZMod p) :
    Lagrange.basis Finset.univ id a = 1 - (X - C a) ^ (p - 1) := by
  apply Polynomial.eq_of_degrees_lt_of_eval_finset_eq (s := Finset.univ)
  · rw [Lagrange.degree_basis (Function.injective_id.injOn) (Finset.mem_univ _)]
    simp only [Finset.card_univ, ZMod.card, Nat.cast_withBot, WithBot.coe_lt_coe]
    exact Nat.sub_lt (Fact.out : p.Prime).pos (by omega)
  · apply lt_of_le_of_lt (degree_sub_le _ _) (max_lt ?_ ?_)
    · simp only [degree_one, Finset.card_univ, ZMod.card]
      exact_mod_cast (Fact.out : p.Prime).pos
    · rw [degree_pow, degree_X_sub_C]
      simp only [Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one, Nat.cast_withBot, WithBot.coe_lt_coe]
      exact Nat.sub_lt (Fact.out : p.Prime).pos (by omega)
  · intro b _
    by_cases hab : a = b
    · subst b
      rw [show (Lagrange.basis Finset.univ id a).eval a = 1 from
        Lagrange.eval_basis_self (v := id) (i := a) Function.injective_id.injOn (Finset.mem_univ _)]
      simp only [eval_sub, eval_one, eval_pow, eval_X, eval_C, sub_self]
      rw [zero_pow (by have hp := (Fact.out : p.Prime).two_le; omega), sub_zero]
    · rw [show (Lagrange.basis Finset.univ id a).eval b = 0 from
      Lagrange.eval_basis_of_ne (v := id) hab (Finset.mem_univ _)]
      simp only [eval_sub, eval_one, eval_pow, eval_X, eval_C, ZMod.pow_card_sub_one]
      rw [if_pos (show b - a ≠ (0 : ZMod p) from sub_ne_zero.mpr (Ne.symm hab)), sub_self]

/-- The prime-field residue projector, expressed as a polynomial in the residue. -/
def primeResidueProjector (N : Module.End (ZMod p) W) (a : ZMod p) : Module.End (ZMod p) W :=
  aeval N (Lagrange.basis Finset.univ id a)

theorem primeResidueProjector_formula (N : Module.End (ZMod p) W) (a : ZMod p) :
    primeResidueProjector p N a = 1 - (N - a • 1) ^ (p - 1) := by
  rw [primeResidueProjector, prime_basis_eq_indicator]
  simp only [map_sub, map_one, map_pow, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one]

/-- The complete family resolves the identity without any finite-dimensionality assumption. -/
theorem sum_primeResidueProjector (N : Module.End (ZMod p) W) :
    ∑ a : ZMod p, primeResidueProjector p N a = 1 := by
  have h := congrArg (aeval N)
    (Lagrange.sum_basis (s := (Finset.univ : Finset (ZMod p)))
      (v := id) Function.injective_id.injOn Finset.univ_nonempty)
  simpa only [map_sum, map_one, primeResidueProjector] using h

private theorem flat_shift_pow (N : Module.End (ZMod p) W) (hN : N ^ p = N) (a : ZMod p) :
    (N - a • 1) ^ p = N - a • 1 := by
  have hp : (X - C a : (ZMod p)[X]) ^ p = X ^ p - C a := by
    rw [sub_pow_char, ← map_pow, ZMod.pow_card]
  have h := congrArg (aeval N) hp
  simpa only [map_pow, map_sub, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one, hN] using h

/-- Zero-curvature residues send each projector into its matching eigenspace. -/
theorem primeResidueProjector_eigen (N : Module.End (ZMod p) W) (hN : N ^ p = N)
    (a : ZMod p) (v : W) :
    N (primeResidueProjector p N a v) = a • primeResidueProjector p N a v := by
  have h : (N - a • 1) * primeResidueProjector p N a = 0 := by
    rw [primeResidueProjector_formula, mul_sub, mul_one, ← pow_succ',
      Nat.sub_add_cancel (Fact.out : p.Prime).one_le, flat_shift_pow p N hN, sub_self]
  have hv := LinearMap.congr_fun h v
  exact sub_eq_zero.mp hv

/-- On a residue eigenvector, the projectors are the Kronecker selectors. -/
theorem primeResidueProjector_apply_eigen (N : Module.End (ZMod p) W)
    (a b : ZMod p) (v : W) (hv : N v = b • v) :
    primeResidueProjector p N a v = if a = b then v else 0 := by
  rw [primeResidueProjector, Module.End.aeval_apply_of_mem_apply_eq_smul hv]
  by_cases hab : a = b
  · subst b
    rw [show (Lagrange.basis Finset.univ id a).eval a = 1 from
        Lagrange.eval_basis_self (v := id) (i := a) Function.injective_id.injOn (Finset.mem_univ _), one_smul, if_pos rfl]
  · rw [show (Lagrange.basis Finset.univ id a).eval b = 0 from
      Lagrange.eval_basis_of_ne (v := id) hab (Finset.mem_univ _), zero_smul, if_neg hab]

/-- A p-flat residue is the direct product of its prime-field eigenspaces. -/
def primeResidueDecomposition (N : Module.End (ZMod p) W) (hN : N ^ p = N) :
    W ≃ₗ[ZMod p] ((a : ZMod p) → N.eigenspace a) where
  toFun v a := ⟨primeResidueProjector p N a v,
    Module.End.mem_eigenspace_iff.mpr (primeResidueProjector_eigen p N hN a v)⟩
  invFun v := ∑ a, (v a : W)
  left_inv v := by
    have h := LinearMap.congr_fun (sum_primeResidueProjector p N) v
    simpa only [LinearMap.sum_apply, Module.End.one_apply] using h
  right_inv v := by
    funext a
    apply Subtype.ext
    change primeResidueProjector p N a (∑ b, (v b : W)) = (v a : W)
    rw [map_sum]
    have hb (b : ZMod p) : primeResidueProjector p N a (v b : W) =
        if a = b then (v b : W) else 0 :=
      primeResidueProjector_apply_eigen p N a b (v b)
        (Module.End.mem_eigenspace_iff.mp (v b).property)
    simp only [hb]
    simp
  map_add' v w := by ext a; exact map_add (primeResidueProjector p N a) v w
  map_smul' c v := by ext a; exact map_smul (primeResidueProjector p N a) c v

/-- Translation of Laurent coefficient degree. -/
def laurentShift (d : ℤ) : (ℤ →₀ W) ≃ₗ[ZMod p] (ℤ →₀ W) :=
  Finsupp.domLCongr
    { toFun := fun n => n + d
      invFun := fun n => n - d
      left_inv := fun n => by dsimp; omega
      right_inv := fun n => by dsimp; omega }

@[simp] theorem laurentShift_apply (d n : ℤ) (f : ℤ →₀ W) :
    laurentShift p d f n = f (n - d) := rfl

/-- Independent integral degree shifts on all residue eigenspaces. -/
def residueShiftMap (N : Module.End (ZMod p) W) (d : ZMod p → ℤ) :
    Module.End (ZMod p) (ℤ →₀ W) :=
  ∑ a : ZMod p, (laurentShift p (d a)).toLinearMap.comp
    (Finsupp.mapRange.linearMap (primeResidueProjector p N a))

@[simp] theorem residueShiftMap_apply (N : Module.End (ZMod p) W)
    (d : ZMod p → ℤ) (f : ℤ →₀ W) (n : ℤ) :
    residueShiftMap p N d f n = ∑ a : ZMod p, primeResidueProjector p N a (f (n - d a)) := by
  simp only [residueShiftMap, LinearMap.sum_apply, Finsupp.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro a _
  rfl

/-- Residue degree shifts compose by addition, even for infinite-dimensional coefficient modules. -/
theorem residueShiftMap_comp (N : Module.End (ZMod p) W) (hN : N ^ p = N)
    (d e : ZMod p → ℤ) :
    residueShiftMap p N d * residueShiftMap p N e = residueShiftMap p N (d + e) := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  change residueShiftMap p N d (residueShiftMap p N e f) n = _
  simp only [residueShiftMap_apply]
  apply Finset.sum_congr rfl
  intro a _
  rw [map_sum]
  have hb (b : ZMod p) (v : W) :
      primeResidueProjector p N a (primeResidueProjector p N b v) =
        if a = b then primeResidueProjector p N b v else 0 :=
    primeResidueProjector_apply_eigen p N a b _ (primeResidueProjector_eigen p N hN b v)
  simp_rw [hb]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Pi.add_apply]
  congr 2
  omega

private theorem residueShiftMap_zero (N : Module.End (ZMod p) W) :
    residueShiftMap p N 0 = 1 := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  simp only [residueShiftMap_apply, Pi.zero_apply, sub_zero]
  simpa only [LinearMap.sum_apply, Module.End.one_apply] using
    LinearMap.congr_fun (sum_primeResidueProjector p N) (f n)

/-- The Laurent gauge shifts the a-eigenspace by the canonical integer representative of a. -/
def laurentResidueGauge (N : Module.End (ZMod p) W) (hN : N ^ p = N) :
    (ℤ →₀ W) ≃ₗ[ZMod p] (ℤ →₀ W) where
  toLinearMap := residueShiftMap p N (fun a => (a.val : ℤ))
  invFun := residueShiftMap p N (fun a => -(a.val : ℤ))
  left_inv f := by
    have h := residueShiftMap_comp p N hN (fun a => -(a.val : ℤ)) (fun a => (a.val : ℤ))
    have he : (fun a : ZMod p => -(a.val : ℤ)) + (fun a => (a.val : ℤ)) = 0 := by
      funext a
      exact neg_add_cancel _
    rw [he, residueShiftMap_zero] at h
    exact LinearMap.congr_fun h f
  right_inv f := by
    have h := residueShiftMap_comp p N hN (fun a => (a.val : ℤ)) (fun a => -(a.val : ℤ))
    have he : (fun a : ZMod p => (a.val : ℤ)) + (fun a => -(a.val : ℤ)) = 0 := by
      funext a
      exact add_neg_cancel _
    rw [he, residueShiftMap_zero] at h
    exact LinearMap.congr_fun h f

/-- Euler minus a constant residue on finite Laurent coefficient lists. -/
def laurentLogarithmicConnection (N : Module.End (ZMod p) W) :
    Module.End (ZMod p) (ℤ →₀ W) where
  toFun f := Finsupp.onFinset f.support (fun n => (n : ZMod p) • f n - N (f n))
    (fun n hn => Finsupp.mem_support_iff.mpr
      (fun h => hn (by rw [h, smul_zero, map_zero, sub_self])))
  map_add' f g := by
    ext n
    simp only [Finsupp.onFinset_apply, Finsupp.add_apply, smul_add, map_add]
    abel
  map_smul' c f := by
    ext n
    change (n : ZMod p) • (c • f n) - N (c • f n) =
      c • ((n : ZMod p) • f n - N (f n))
    rw [map_smul, smul_sub, smul_comm (n : ZMod p) c]

@[simp] theorem laurentLogarithmicConnection_apply (N : Module.End (ZMod p) W)
    (f : ℤ →₀ W) (n : ℤ) :
    laurentLogarithmicConnection p N f n = (n : ZMod p) • f n - N (f n) := rfl

private theorem laurentConnection_pow_apply (N : Module.End (ZMod p) W)
    (k : ℕ) (f : ℤ →₀ W) (n : ℤ) :
    (laurentLogarithmicConnection p N ^ k) f n =
      (((n : ZMod p) • (1 : Module.End (ZMod p) W) - N) ^ k) (f n) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', Module.End.mul_apply, laurentLogarithmicConnection_apply, ih,
      pow_succ', Module.End.mul_apply]
    rfl

/-- Laurent coefficients have the same constant p-curvature as polynomial coefficients. -/
theorem laurent_pcurvature (N : Module.End (ZMod p) W) :
    laurentLogarithmicConnection p N ^ p - laurentLogarithmicConnection p N =
      Finsupp.mapRange.linearMap (residueCurvature p N) := by
  apply LinearMap.ext
  intro f
  apply Finsupp.ext
  intro n
  have h := congrArg (fun T : Module.End (ZMod p) (ℕ →₀ W) =>
    T (Finsupp.single (n : ZMod p).val (f n)) (n : ZMod p).val)
      (logarithmic_pcurvature p N)
  simp only [LinearMap.sub_apply, Finsupp.sub_apply, logarithmicConnection_pow_apply,
    logarithmicConnection_apply, Finsupp.single_eq_same, lift_apply,
    ZMod.natCast_zmod_val] at h
  change (laurentLogarithmicConnection p N ^ p) f n -
    laurentLogarithmicConnection p N f n = residueCurvature p N (f n)
  rw [laurentConnection_pow_apply]
  exact h

/-- Zero Laurent p-curvature is exactly the prime-field polynomial relation on the residue. -/
theorem laurent_pcurvature_zero_iff (N : Module.End (ZMod p) W) :
    laurentLogarithmicConnection p N ^ p - laurentLogarithmicConnection p N = 0 ↔ N ^ p = N := by
  rw [laurent_pcurvature]
  constructor
  · intro h
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun T : Module.End (ZMod p) (ℤ →₀ W) => T (Finsupp.single 0 v) 0) h
    change residueCurvature p N (Finsupp.single 0 v 0) = 0 at hv
    rw [Finsupp.single_eq_same] at hv
    exact (sub_eq_zero.mp hv).symm
  · intro h
    have he : residueCurvature p N = 0 := sub_eq_zero.mpr h.symm
    rw [he]
    apply LinearMap.ext
    intro f
    apply Finsupp.ext
    intro n
    rfl

/-- Every p-flat Laurent logarithmic connection is explicitly gauge-equivalent to Euler. -/
theorem laurentResidueGauge_intertwines (N : Module.End (ZMod p) W) (hN : N ^ p = N)
    (f : ℤ →₀ W) :
    laurentLogarithmicConnection p N (laurentResidueGauge p N hN f) =
      laurentResidueGauge p N hN (laurentLogarithmicConnection p 0 f) := by
  apply Finsupp.ext
  intro n
  change laurentLogarithmicConnection p N
    (residueShiftMap p N (fun a => (a.val : ℤ)) f) n =
      residueShiftMap p N (fun a => (a.val : ℤ)) (laurentLogarithmicConnection p 0 f) n
  simp only [laurentLogarithmicConnection_apply, residueShiftMap_apply,
    Finset.smul_sum, map_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [primeResidueProjector_eigen p N hN,
    LinearMap.zero_apply, sub_zero, map_smul,
    Int.cast_sub, Int.cast_natCast, ZMod.natCast_zmod_val, sub_smul]

/-- The residue gauge commutes with all Laurent monomial multiplications. -/
theorem laurentResidueGauge_shift (N : Module.End (ZMod p) W) (hN : N ^ p = N)
    (d : ℤ) (f : ℤ →₀ W) :
    laurentResidueGauge p N hN (laurentShift p d f) =
      laurentShift p d (laurentResidueGauge p N hN f) := by
  apply Finsupp.ext
  intro n
  change residueShiftMap p N (fun a => (a.val : ℤ)) (laurentShift p d f) n =
    laurentShift p d (residueShiftMap p N (fun a => (a.val : ℤ)) f) n
  simp only [residueShiftMap_apply, laurentShift_apply]
  apply Finset.sum_congr rfl
  intro a _
  apply congrArg (primeResidueProjector p N a)
  apply congrArg f
  omega

/-- Zero p-curvature exactly characterizes Laurent gauge equivalence to Euler. -/
theorem laurent_gauge_iff_zero_curvature (N : Module.End (ZMod p) W) :
    (∃ G : (ℤ →₀ W) ≃ₗ[ZMod p] (ℤ →₀ W),
      (∀ d f, G (laurentShift p d f) = laurentShift p d (G f)) ∧
      ∀ f, laurentLogarithmicConnection p N (G f) = G (laurentLogarithmicConnection p 0 f)) ↔
      laurentLogarithmicConnection p N ^ p - laurentLogarithmicConnection p N = 0 := by
  constructor
  · rintro ⟨G, _, hG⟩
    have hpow (k : ℕ) (f : ℤ →₀ W) :
        (laurentLogarithmicConnection p N ^ k) (G f) =
          G ((laurentLogarithmicConnection p 0 ^ k) f) := by
      induction k with
      | zero => rfl
      | succ k ih =>
        rw [pow_succ', Module.End.mul_apply, ih, hG, pow_succ', Module.End.mul_apply]
    have hE : laurentLogarithmicConnection p (0 : Module.End (ZMod p) W) ^ p =
        laurentLogarithmicConnection p 0 := by
      apply sub_eq_zero.mp
      apply (laurent_pcurvature_zero_iff p 0).mpr
      exact zero_pow (Fact.out : p.Prime).ne_zero
    apply LinearMap.ext
    intro y
    obtain ⟨f, rfl⟩ := G.surjective y
    change (laurentLogarithmicConnection p N ^ p) (G f) -
      laurentLogarithmicConnection p N (G f) = 0
    rw [hpow, hG, hE, sub_self]
  · intro hD
    let hN := (laurent_pcurvature_zero_iff p N).mp hD
    exact ⟨laurentResidueGauge p N hN, laurentResidueGauge_shift p N hN,
      laurentResidueGauge_intertwines p N hN⟩

/-- Horizontal Euler coefficients are supported exactly in degrees divisible by p. -/
theorem laurentEuler_kernel_iff (f : ℤ →₀ W) :
    laurentLogarithmicConnection p 0 f = 0 ↔
      f ∈ Finsupp.supported W (ZMod p) {n : ℤ | (n : ZMod p) = 0} := by
  rw [Finsupp.mem_supported']
  constructor
  · intro hf n hn
    have h := congrArg (fun g : ℤ →₀ W => g n) hf
    change (n : ZMod p) • f n - 0 = 0 at h
    rw [sub_zero] at h
    exact (smul_eq_zero.mp h).resolve_left hn
  · intro hf
    apply Finsupp.ext
    intro n
    change (n : ZMod p) • f n - 0 = 0
    by_cases hn : (n : ZMod p) = 0
    · rw [hn, zero_smul, sub_self]
    · rw [hf n hn, smul_zero, sub_self]

private def eulerSupportEquiv :
    LinearMap.ker (laurentLogarithmicConnection p (0 : Module.End (ZMod p) W)) ≃ₗ[ZMod p]
      Finsupp.supported W (ZMod p) {n : ℤ | (n : ZMod p) = 0} where
  toFun f := ⟨f.val, (laurentEuler_kernel_iff p f.val).mp f.property⟩
  invFun f := ⟨f.val, (laurentEuler_kernel_iff p f.val).mpr f.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Multiplication by p identifies all integral degrees with the horizontal degrees. -/
def primeMultipleIndex : ℤ ≃ {n : ℤ // (n : ZMod p) = 0} :=
  Equiv.ofBijective (fun n : ℤ => ⟨(p : ℤ) * n, by
    rw [Int.cast_mul, Int.cast_natCast, CharP.cast_eq_zero (ZMod p) p, zero_mul]⟩)
    (by
      constructor
      · intro a b h
        have hp : (p : ℤ) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
        exact mul_left_cancel₀ hp (congrArg Subtype.val h)
      · intro n
        obtain ⟨a, ha⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd n.val p).mp n.property
        exact ⟨a, Subtype.ext ha.symm⟩)

/-- Frobenius degree dilation identifies free Laurent coefficients with Euler-horizontal sections. -/
def laurentEulerCartierEquiv :
    (ℤ →₀ W) ≃ₗ[ZMod p]
      LinearMap.ker (laurentLogarithmicConnection p (0 : Module.End (ZMod p) W)) :=
  (Finsupp.domLCongr (primeMultipleIndex p)).trans
    ((Finsupp.supportedEquivFinsupp (R := ZMod p)
      {n : ℤ | (n : ZMod p) = 0}).symm.trans (eulerSupportEquiv p).symm)

/-- The residue gauge identifies horizontal subspaces of the two logarithmic connections. -/
def laurentHorizontalGauge (N : Module.End (ZMod p) W) (hN : N ^ p = N) :
    LinearMap.ker (laurentLogarithmicConnection p (0 : Module.End (ZMod p) W)) ≃ₗ[ZMod p]
      LinearMap.ker (laurentLogarithmicConnection p N) where
  toFun f := ⟨laurentResidueGauge p N hN f.val, by
    rw [LinearMap.mem_ker, laurentResidueGauge_intertwines, f.property, map_zero]⟩
  invFun f := ⟨(laurentResidueGauge p N hN).symm f.val, by
    apply (laurentResidueGauge p N hN).injective
    rw [map_zero, ← laurentResidueGauge_intertwines, LinearEquiv.apply_symm_apply]
    exact f.property⟩
  left_inv f := Subtype.ext ((laurentResidueGauge p N hN).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((laurentResidueGauge p N hN).apply_symm_apply f.val)
  map_add' f g := Subtype.ext (map_add (laurentResidueGauge p N hN) f.val g.val)
  map_smul' c f := Subtype.ext (map_smul (laurentResidueGauge p N hN) c f.val)

/-- Explicit Cartier descent for every p-flat constant-residue Laurent connection. -/
def laurentCartierEquiv (N : Module.End (ZMod p) W) (hN : N ^ p = N) :
    (ℤ →₀ W) ≃ₗ[ZMod p] LinearMap.ker (laurentLogarithmicConnection p N) :=
  (laurentEulerCartierEquiv p).trans (laurentHorizontalGauge p N hN)

/-- Frobenius dilation sends a monomial coefficient to degree p times its original degree. -/
theorem laurentEulerCartierEquiv_single (n : ℤ) (v : W) :
    (laurentEulerCartierEquiv p (Finsupp.single n v) : ℤ →₀ W) =
      Finsupp.single ((p : ℤ) * n) v := by
  simp only [laurentEulerCartierEquiv, LinearEquiv.trans_apply, Finsupp.domLCongr_single]
  change ((Finsupp.supportedEquivFinsupp (R := ZMod p)
      {n : ℤ | (n : ZMod p) = 0}).symm
        (Finsupp.single (primeMultipleIndex p n) v) : ℤ →₀ W) = _
  rw [Finsupp.supportedEquivFinsupp_symm_single]
  rfl

/-- Cartier descent places each residue component at its exact congruence-class degree. -/
theorem laurentCartierEquiv_single (N : Module.End (ZMod p) W) (hN : N ^ p = N)
    (n : ℤ) (v : W) :
    (laurentCartierEquiv p N hN (Finsupp.single n v) : ℤ →₀ W) =
      ∑ a : ZMod p, Finsupp.single ((p : ℤ) * n + (a.val : ℤ))
        (primeResidueProjector p N a v) := by
  change residueShiftMap p N (fun a => (a.val : ℤ))
    (laurentEulerCartierEquiv p (Finsupp.single n v) : ℤ →₀ W) = _
  rw [laurentEulerCartierEquiv_single]
  simp only [residueShiftMap, LinearMap.sum_apply, LinearMap.comp_apply]
  apply Finset.sum_congr rfl
  intro a _
  change laurentShift p (a.val : ℤ)
    (Finsupp.mapRange (primeResidueProjector p N a) (map_zero _) (Finsupp.single _ v)) = _
  rw [Finsupp.mapRange_single]
  exact Finsupp.domLCongr_single _ _ _

/-- Cartier descent respects Laurent multiplication through Frobenius degree dilation. -/
theorem laurentCartierEquiv_shift (N : Module.End (ZMod p) W) (hN : N ^ p = N)
    (k : ℤ) (f : ℤ →₀ W) :
    (laurentCartierEquiv p N hN (laurentShift p k f) : ℤ →₀ W) =
      laurentShift p ((p : ℤ) * k) (laurentCartierEquiv p N hN f : ℤ →₀ W) := by
  let C : Module.End (ZMod p) (ℤ →₀ W) :=
    (LinearMap.ker (laurentLogarithmicConnection p N)).subtype.comp
      (laurentCartierEquiv p N hN).toLinearMap
  have hc (n : ℤ) (v : W) : C (Finsupp.single n v) =
      ∑ a : ZMod p, Finsupp.single ((p : ℤ) * n + (a.val : ℤ))
        (primeResidueProjector p N a v) := laurentCartierEquiv_single p N hN n v
  have hs (n : ℤ) (v : W) : C (laurentShift p k (Finsupp.single n v)) =
      laurentShift p ((p : ℤ) * k) (C (Finsupp.single n v)) := by
    rw [show laurentShift p k (Finsupp.single n v) = Finsupp.single (n + k) v from
      Finsupp.domLCongr_single _ _ _, hc, hc, map_sum]
    apply Finset.sum_congr rfl
    intro a _
    rw [show laurentShift p ((p : ℤ) * k)
      (Finsupp.single ((p : ℤ) * n + (a.val : ℤ)) (primeResidueProjector p N a v)) =
        Finsupp.single (((p : ℤ) * n + (a.val : ℤ)) + (p : ℤ) * k)
          (primeResidueProjector p N a v) from Finsupp.domLCongr_single _ _ _]
    congr 1
    ring
  change C (laurentShift p k f) = laurentShift p ((p : ℤ) * k) (C f)
  induction f using Finsupp.induction with
  | zero => simp only [map_zero]
  | single_add n v f _ _ ih => rw [map_add, map_add, map_add, map_add, hs, ih]

/-- Vanishing p-curvature alone supplies the explicit Cartier isomorphism. -/
def laurentCartierOfZeroCurvature (N : Module.End (ZMod p) W)
    (hD : laurentLogarithmicConnection p N ^ p - laurentLogarithmicConnection p N = 0) :
    (ℤ →₀ W) ≃ₗ[ZMod p] LinearMap.ker (laurentLogarithmicConnection p N) :=
  laurentCartierEquiv p N ((laurent_pcurvature_zero_iff p N).mp hD)

#print axioms laurentCartierEquiv_shift
#print axioms laurentResidueGauge_shift
#print axioms laurent_gauge_iff_zero_curvature
#print axioms laurent_pcurvature_zero_iff
#print axioms laurentCartierOfZeroCurvature
#print axioms laurentCartierEquiv
#print axioms laurentCartierEquiv_single
#print axioms laurentResidueGauge_intertwines
#print axioms laurentResidueGauge
#print axioms primeResidueDecomposition
end GaloisForLFunctions.RepresentationLifting.DividedPower
