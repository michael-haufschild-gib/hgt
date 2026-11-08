import GaloisForLFunctions.InfiniteRankWeilTheory.ReturnsFreezeSmoothPolynomials
import GaloisForLFunctions.HTGeometry.AlgebraicIntegerSeparation
import GaloisForLFunctions.HTGeometry.KroneckerApproxRecurrence
import GaloisForLFunctions.HTGeometry.ArchimedeanCorank

/-!
# The Frobenius of the torsion is Galois

Stepanov's count over `𝔽_q` uses that the Frobenius is a ring endomorphism fixing every rational
point. Over `ℤ` a `P`-smooth integer Dirichlet polynomial `A(s) = Σ a_n n^{-s}` is an integer
polynomial `F` on the prime torus, `A(s) = F((p^{-s})_{p ∈ P})`, and the Adams operation
`ψ_a F = F(u^a)` is a ring endomorphism (`adams`). It acts in two ways.

* On the **prime orbit** `u = (p^{-it})_p` it is the dilation `t ↦ at` (`orbitValue_adams`). Two
  primes have no common torsion return besides `t = 0` (`eq_zero_of_torsion_return`), so on the orbit
  the Frobenius has the single fixed point `0`.
* On a **torsion point** `μ^b = (μ^{b_p})_p`, `μ` a primitive `m`-th root of unity, it is the Galois
  action of `ℚ(μ_m)`: `ψ_a F(μ^b) = F((μ^a)^b)` (`aeval_torsionPoint_adams`), and the conjugates of
  `F(μ^b)` are its values on the **closed point** `{μ'^b : μ'` primitive`}` (`aeval_torsionPoint`). On
  the `(q−1)`-torsion `ψ_q F = F` (`aeval_torsionPoint_adams_of_pow_eq`): the identity `x^q = x` holds
  exactly, in characteristic zero.

**The norm amplifier.** The product of `|F|` over a closed point is the modulus of the norm of a
cyclotomic integer: it is `0` or at least `1` (`one_le_prod_norm_aeval_primitiveRoots`), and a product
below `1` forces `F` to vanish on the whole closed point (`torus_norm_amplifier`); the threshold `1` is
attained by `F = 1` (`norm_amplifier_threshold_sharp`). The same holds for every partial derivative,
so the amplifier works at every uniform order (`vanishesToOrder_of_small`).

**On the orbit.** The prime orbit returns to every torsion point at arbitrarily large heights
(`exists_torsion_return`), and the dilates `at` of a `δ`-return to `μ^b` are `aδ`-returns to its
conjugates `(μ^a)^b`. So if `A` is small at the heights `at`, `a < m` prime to `m`, of one torsion
return, then `F` vanishes exactly on the closed point (`eq_zero_of_small_on_frobeniusOrbit`), and at
every torsion return where `F` does not vanish the Frobenius orbit carries
`Π_a (|A(iat)| + aδ L(F)) ≥ 1` (`one_le_prod_frobeniusOrbit`), `L(F) = Σ |c_α| |α|`. The precision
needed is `δ ≤ 1/(4m L(F))`, with no factorial (`eq_zero_of_frobeniusOrbit_le_half`): exactness is
reached on the torus at a precision the Rouché copy of a zero on the orbit cannot use
(`InfiniteRankWeilTheory.order_le_of_rouche`).
-/

open Polynomial Finset NumberField

noncomputable section

namespace GaloisForLFunctions.ArithmeticLefschetzStepanovTheory

open InfiniteRankWeilTheory

/-! ### The norm of a value at a primitive root of unity -/

/-- Primitive `m`-th roots of unity are the powers `μ^a`, `a < m` prime to `m`, of one of them. -/
theorem prod_primitiveRoots_eq {m : ℕ} (hm : 0 < m) {μ : ℂ} (hμ : IsPrimitiveRoot μ m)
    (f : ℂ → ℝ) :
    ∏ μ' ∈ primitiveRoots m ℂ, f μ' = ∏ a ∈ (range m).filter (m.Coprime ·), f (μ ^ a) := by
  haveI : NeZero m := ⟨hm.ne'⟩
  symm
  refine Finset.prod_nbij (fun a => μ ^ a) ?_ ?_ ?_ (fun _ _ => rfl)
  · intro a ha
    rw [mem_filter, mem_range] at ha
    rw [mem_primitiveRoots hm]
    exact hμ.pow_of_coprime a ha.2.symm
  · intro a ha b hb hab
    rw [Finset.mem_coe, mem_filter, mem_range] at ha hb
    exact hμ.pow_inj ha.1 hb.1 hab
  · intro ξ hξ
    rw [Finset.mem_coe, mem_primitiveRoots hm, hμ.isPrimitiveRoot_iff] at hξ
    obtain ⟨i, hi, hic, rfl⟩ := hξ
    exact ⟨i, by rw [Finset.mem_coe, mem_filter, mem_range]; exact ⟨hi, hic.symm⟩, rfl⟩

/-- Ring homomorphisms commute with evaluation of integer polynomials. -/
theorem map_aeval_int {A B : Type*} [CommRing A] [CommRing B] (φ : A →+* B) (x : A) (G : ℤ[X]) :
    φ (aeval x G) = aeval (φ x) G := by
  rw [aeval_def, aeval_def, hom_eval₂]
  congr 1
  exact RingHom.ext_int _ _

/-- **The norm bound.** If an integer polynomial does not vanish at some primitive `m`-th root of
unity, the product of its moduli over all primitive `m`-th roots is at least `1`: it is the modulus of
the norm of a nonzero cyclotomic integer. -/
theorem one_le_prod_norm_aeval_primitiveRoots {m : ℕ} (hm : 0 < m) (G : ℤ[X])
    (hG : ∃ μ ∈ primitiveRoots m ℂ, aeval μ G ≠ 0) :
    1 ≤ ∏ μ ∈ primitiveRoots m ℂ, ‖aeval μ G‖ := by
  classical
  letI : NeZero m := ⟨hm.ne'⟩
  let K := CyclotomicField m ℚ
  letI : IsCyclotomicExtension {m} ℚ K := CyclotomicField.isCyclotomicExtension m ℚ
  have hζ : IsPrimitiveRoot (IsCyclotomicExtension.zeta m ℚ K) m :=
    IsCyclotomicExtension.zeta_spec m ℚ K
  set ζ : K := IsCyclotomicExtension.zeta m ℚ K
  let β : 𝓞 K := aeval hζ.toInteger G
  have hcoe : (β : K) = aeval ζ G := by
    change algebraMap (𝓞 K) K (aeval hζ.toInteger G) = _
    rw [map_aeval_int]
    rfl
  have hemb (σ : K →ₐ[ℚ] ℂ) : σ (β : K) = aeval (σ ζ) G := by
    rw [hcoe]
    exact map_aeval_int σ.toRingHom ζ G
  let e := hζ.embeddingsEquivPrimitiveRoots ℂ (cyclotomic.irreducible_rat hm)
  have hβ : β ≠ 0 := by
    obtain ⟨μ, hμ, hGμ⟩ := hG
    obtain ⟨σ, hσ⟩ := e.surjective ⟨μ, hμ⟩
    have hσμ : σ ζ = μ := by
      have h := congrArg Subtype.val hσ
      rwa [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe] at h
    intro h0
    apply hGμ
    rw [← hσμ, ← hemb σ, h0]
    simp
  have hp := HTGeometry.one_le_prod_norm_embeddings β hβ
  have he : (∏ σ : K →+* ℂ, ‖σ (β : K)‖) = ∏ μ ∈ primitiveRoots m ℂ, ‖aeval μ G‖ := by
    calc
      _ = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ (β : K)‖ :=
        Fintype.prod_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)) _ _ (fun _ => rfl)
      _ = ∏ σ : K →ₐ[ℚ] ℂ, ‖aeval (σ ζ) G‖ := prod_congr rfl fun σ _ => by rw [hemb σ]
      _ = _ := by
        rw [← prod_coe_sort (primitiveRoots m ℂ)]
        exact Fintype.prod_equiv e _ _
          (fun σ => by rw [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe])
  rwa [he] at hp

/-- **A closed point vanishes as a whole.** An integer polynomial vanishing at one primitive `m`-th
root of unity vanishes at all of them: their minimal polynomial is the cyclotomic polynomial. -/
theorem aeval_eq_zero_of_mem_primitiveRoots {m : ℕ} (hm : 0 < m) (G : ℤ[X]) {μ₀ μ : ℂ}
    (hμ₀ : μ₀ ∈ primitiveRoots m ℂ) (h0 : aeval μ₀ G = 0) (hμ : μ ∈ primitiveRoots m ℂ) :
    aeval μ G = 0 := by
  haveI : NeZero (m : ℂ) := ⟨by exact_mod_cast hm.ne'⟩
  have h₀ : IsPrimitiveRoot μ₀ m := (mem_primitiveRoots hm).mp hμ₀
  have h₁ : IsPrimitiveRoot μ m := (mem_primitiveRoots hm).mp hμ
  have hq (x : ℂ) : aeval x (G.map (algebraMap ℤ ℚ)) = aeval x G := aeval_map_algebraMap ℚ x G
  have hdvd : minpoly ℚ μ₀ ∣ G.map (algebraMap ℤ ℚ) := minpoly.dvd ℚ μ₀ (by rw [hq]; exact h0)
  rw [← cyclotomic_eq_minpoly_rat h₀ hm] at hdvd
  obtain ⟨r, hr⟩ := hdvd
  have hroot : aeval μ (cyclotomic m ℚ) = 0 := by
    rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (isRoot_cyclotomic_iff.mpr h₁)
  rw [← hq, hr, map_mul, hroot, zero_mul]

/-- **The norm amplifier.** If the product of `|G|` over the primitive `m`-th roots of unity is
below `1`, then `G` vanishes at every primitive `m`-th root of unity. -/
theorem norm_amplifier {m : ℕ} (hm : 0 < m) (G : ℤ[X])
    (hsmall : ∏ μ ∈ primitiveRoots m ℂ, ‖aeval μ G‖ < 1) :
    ∀ μ ∈ primitiveRoots m ℂ, aeval μ G = 0 := by
  by_contra h
  push Not at h
  exact absurd (one_le_prod_norm_aeval_primitiveRoots hm G h) (not_le.mpr hsmall)

/-- The threshold `1` of the amplifier is sharp: the constant `1` has product `1` and no zero. -/
theorem norm_amplifier_threshold_sharp (m : ℕ) :
    ∏ μ ∈ primitiveRoots m ℂ, ‖aeval μ (1 : ℤ[X])‖ = 1 ∧
      ∀ μ : ℂ, aeval μ (1 : ℤ[X]) ≠ 0 := by
  simp

/-! ### The Frobenius on the torus -/

variable {σ : Type*}

/-- The Adams operation `ψ_a F = F(u^a)`: a ring endomorphism of the integer auxiliaries. -/
def adams (a : ℕ) : MvPolynomial σ ℤ →ₐ[ℤ] MvPolynomial σ ℤ :=
  MvPolynomial.aeval fun i => MvPolynomial.X i ^ a

theorem aeval_adams (a : ℕ) (u : σ → ℂ) (F : MvPolynomial σ ℤ) :
    MvPolynomial.aeval u (adams a F) = MvPolynomial.aeval (fun i => u i ^ a) F := by
  rw [adams, MvPolynomial.comp_aeval_apply]
  simp

/-- The torsion point `μ^b = (μ^{b_i})_i`. -/
def torsionPoint (μ : ℂ) (b : σ → ℕ) : σ → ℂ := fun i => μ ^ b i

/-- The one-variable polynomial `F(X^b)` whose values at roots of unity are the values of `F` at
torsion points. -/
def pullback (b : σ → ℕ) (F : MvPolynomial σ ℤ) : ℤ[X] :=
  MvPolynomial.aeval (fun i => (X : ℤ[X]) ^ b i) F

theorem aeval_torsionPoint (μ : ℂ) (b : σ → ℕ) (F : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (torsionPoint μ b) F = aeval μ (pullback b F) := by
  rw [pullback, MvPolynomial.comp_aeval_apply]
  simp only [map_pow, Polynomial.aeval_X]
  rfl

/-- **The Frobenius on torsion is Galois.** `ψ_a F` at `μ^b` is `F` at the conjugate torsion point
`(μ^a)^b`. -/
theorem aeval_torsionPoint_adams (a : ℕ) (μ : ℂ) (b : σ → ℕ) (F : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (torsionPoint μ b) (adams a F) =
      MvPolynomial.aeval (torsionPoint (μ ^ a) b) F := by
  rw [aeval_adams]
  have h : (fun i => torsionPoint μ b i ^ a) = torsionPoint (μ ^ a) b := by
    funext i
    simp only [torsionPoint, ← pow_mul, mul_comm]
  rw [h]

/-- **`x^q = x` on the torsion.** On a torsion point of order dividing `q − 1`, `ψ_q F = F`. -/
theorem aeval_torsionPoint_adams_of_pow_eq {q : ℕ} {μ : ℂ} (hμ : μ ^ q = μ) (b : σ → ℕ)
    (F : MvPolynomial σ ℤ) :
    MvPolynomial.aeval (torsionPoint μ b) (adams q F) = MvPolynomial.aeval (torsionPoint μ b) F := by
  rw [aeval_torsionPoint_adams, hμ]

/-- **The norm amplifier on the torus.** If the product of `|F|` over the closed point
`{μ^b : μ` primitive`}` is below `1`, then `F` vanishes on the whole closed point. -/
theorem torus_norm_amplifier {m : ℕ} (hm : 0 < m) (F : MvPolynomial σ ℤ) (b : σ → ℕ)
    (hsmall : ∏ μ ∈ primitiveRoots m ℂ, ‖MvPolynomial.aeval (torsionPoint μ b) F‖ < 1) :
    ∀ μ ∈ primitiveRoots m ℂ, MvPolynomial.aeval (torsionPoint μ b) F = 0 := by
  simp_rw [aeval_torsionPoint] at hsmall ⊢
  exact norm_amplifier hm _ hsmall

/-- Iterated partial derivatives along a list of variables. -/
def iterDeriv (F : MvPolynomial σ ℤ) (l : List σ) : MvPolynomial σ ℤ :=
  l.foldr (fun i G => MvPolynomial.pderiv i G) F

/-- `F` vanishes to uniform order `J` at a point: all partial derivatives of order `< J` vanish. -/
def VanishesToOrder (F : MvPolynomial σ ℤ) (ω : σ → ℂ) (J : ℕ) : Prop :=
  ∀ l : List σ, l.length < J → MvPolynomial.aeval ω (iterDeriv F l) = 0

/-- **The amplifier at every order.** Partial derivatives of integer auxiliaries are integer
auxiliaries, so small derivative norms on a closed point give exact vanishing to that order. -/
theorem vanishesToOrder_of_small {m : ℕ} (hm : 0 < m) (F : MvPolynomial σ ℤ) (b : σ → ℕ) (J : ℕ)
    (hsmall : ∀ l : List σ, l.length < J →
      ∏ μ ∈ primitiveRoots m ℂ, ‖MvPolynomial.aeval (torsionPoint μ b) (iterDeriv F l)‖ < 1) :
    ∀ μ ∈ primitiveRoots m ℂ, VanishesToOrder F (torsionPoint μ b) J :=
  fun μ hμ l hl => torus_norm_amplifier hm _ b (hsmall l hl) μ hμ

/-! ### Lipschitz control on the closed polydisc -/

/-- Products of numbers in the closed unit disc move by at most the sum of the moves. -/
theorem norm_prod_sub_prod_le {ι : Type*} (s : Finset ι) (x y : ι → ℂ)
    (hx : ∀ i ∈ s, ‖x i‖ ≤ 1) (hy : ∀ i ∈ s, ‖y i‖ ≤ 1) :
    ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ∑ i ∈ s, ‖x i - y i‖ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [prod_insert ha, prod_insert ha, sum_insert ha]
    have hxa := hx a (mem_insert_self a s)
    have hys : ‖∏ i ∈ s, y i‖ ≤ 1 := by
      rw [norm_prod]
      exact prod_le_one (fun _ _ => norm_nonneg _) (fun i hi => hy i (mem_insert_of_mem hi))
    have ih' := ih (fun i hi => hx i (mem_insert_of_mem hi)) (fun i hi => hy i (mem_insert_of_mem hi))
    have hsplit : x a * ∏ i ∈ s, x i - y a * ∏ i ∈ s, y i =
        x a * (∏ i ∈ s, x i - ∏ i ∈ s, y i) + (x a - y a) * ∏ i ∈ s, y i := by ring
    rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    rw [norm_mul, norm_mul]
    have h1 : ‖x a‖ * ‖∏ i ∈ s, x i - ∏ i ∈ s, y i‖ ≤ ∑ i ∈ s, ‖x i - y i‖ :=
      (mul_le_of_le_one_left (norm_nonneg _) hxa).trans ih'
    have h2 : ‖x a - y a‖ * ‖∏ i ∈ s, y i‖ ≤ ‖x a - y a‖ :=
      mul_le_of_le_one_right (norm_nonneg _) hys
    linarith

/-- `|x^k − y^k| ≤ k|x − y|` in the closed unit disc. -/
theorem norm_pow_sub_pow_le {x y : ℂ} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) (k : ℕ) :
    ‖x ^ k - y ^ k‖ ≤ k * ‖x - y‖ := by
  have h := norm_prod_sub_prod_le (range k) (fun _ => x) (fun _ => y) (fun _ _ => hx)
    (fun _ _ => hy)
  simpa [prod_const, sum_const, card_range, nsmul_eq_mul] using h

/-- The Lipschitz weight `L(F) = Σ_α |c_α| |α|` of an integer auxiliary. -/
def lipWeight (F : MvPolynomial σ ℤ) : ℝ :=
  ∑ d ∈ F.support, |((MvPolynomial.coeff d F : ℤ) : ℝ)| * ∑ i ∈ d.support, (d i : ℝ)

theorem lipWeight_nonneg (F : MvPolynomial σ ℤ) : 0 ≤ lipWeight F :=
  sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (sum_nonneg fun _ _ => Nat.cast_nonneg _)

/-- **Lipschitz bound.** On the closed unit polydisc, `|F(u) − F(v)| ≤ L(F) · max |u_i − v_i|`. -/
theorem norm_aeval_sub_le (F : MvPolynomial σ ℤ) {u v : σ → ℂ} {δ : ℝ} (hu : ∀ i, ‖u i‖ ≤ 1)
    (hv : ∀ i, ‖v i‖ ≤ 1) (huv : ∀ i, ‖u i - v i‖ ≤ δ) :
    ‖MvPolynomial.aeval u F - MvPolynomial.aeval v F‖ ≤ lipWeight F * δ := by
  rw [MvPolynomial.aeval_def, MvPolynomial.aeval_def, MvPolynomial.eval₂_eq,
    MvPolynomial.eval₂_eq, ← sum_sub_distrib, lipWeight, sum_mul]
  refine (norm_sum_le _ _).trans (sum_le_sum fun d _ => ?_)
  rw [← mul_sub, norm_mul, algebraMap_int_eq, eq_intCast, Complex.norm_intCast, mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
  refine (norm_prod_sub_prod_le d.support _ _
    (fun i _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hu i))
    (fun i _ => by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) (hv i))).trans ?_
  rw [sum_mul]
  exact sum_le_sum fun i _ => (norm_pow_sub_pow_le (hu i) (hv i) (d i)).trans
    (mul_le_mul_of_nonneg_left (huv i) (Nat.cast_nonneg _))

/-! ### The prime orbit and its torsion returns -/

variable {P : Finset Nat.Primes}

/-- The point `(p^{-it})_{p ∈ P}` of the prime orbit. -/
def orbitPoint (P : Finset Nat.Primes) (t : ℝ) : P → ℂ :=
  fun p => phase ((p : Nat.Primes) : ℕ) t

/-- The value `A(it) = F((p^{-it})_p)` of the auxiliary on the prime orbit. -/
def orbitValue (F : MvPolynomial P ℤ) (t : ℝ) : ℂ :=
  MvPolynomial.aeval (orbitPoint P t) F

theorem phase_nat_mul (n a : ℕ) (t : ℝ) : phase n (a * t) = phase n t ^ a := by
  rw [phase, phase, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- **The Frobenius on the orbit is the dilation.** `ψ_a F` at height `t` is `F` at height `at`. -/
theorem orbitValue_adams (a : ℕ) (F : MvPolynomial P ℤ) (t : ℝ) :
    orbitValue (adams a F) t = orbitValue F (a * t) := by
  rw [orbitValue, aeval_adams, orbitValue]
  have h : (fun p => orbitPoint P t p ^ a) = orbitPoint P (a * t) := by
    funext p
    simp only [orbitPoint, phase_nat_mul]
  rw [h]

/-- **No common torsion return.** If the phases of two distinct primes are both `m`-th roots of unity
at height `t`, then `t = 0`. -/
theorem eq_zero_of_torsion_return {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) {m : ℕ}
    (hm : 0 < m) {t : ℝ} (htp : phase p t ^ m = 1) (htq : phase q t ^ m = 1) : t = 0 := by
  rw [← phase_nat_mul] at htp htq
  have h := eq_zero_of_exact_return hp hq hpq htp htq
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  exact (mul_eq_zero.mp h).resolve_left hm'

/-- **Torsion returns exist at every height.** The prime orbit comes within `δ` of every torsion
point `ζ_m^b`, `ζ_m = e^{2πi/m}`, at arbitrarily large heights (Kronecker). -/
theorem exists_torsion_return (P : Finset Nat.Primes) {m : ℕ} (b : P → ℕ) {δ : ℝ} (hδ : 0 < δ)
    (T₀ : ℝ) :
    ∃ t : ℝ, T₀ < t ∧ ∀ p : P,
      ‖orbitPoint P t p - Complex.exp (2 * Real.pi * Complex.I / m) ^ b p‖ < δ := by
  classical
  obtain ⟨t, ht, hclose⟩ := kronecker_approx_atTop (primeLogFiniteSlice_linearIndependent P)
    (fun p => -(2 * Real.pi * b p / m)) hδ T₀
  refine ⟨t, ht, fun p => ?_⟩
  have hconj : orbitPoint P t p = (starRingEnd ℂ) (expChar (Real.log ((p : Nat.Primes) : ℕ)) t) := by
    rw [orbitPoint, phase, expChar, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  have htarget : Complex.exp (2 * Real.pi * Complex.I / m) ^ b p =
      (starRingEnd ℂ) (Complex.exp (((-(2 * Real.pi * b p / m) : ℝ) : ℂ) * Complex.I)) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring
  rw [hconj, htarget, ← map_sub, Complex.norm_conj]
  exact hclose p

/-- The dilates of a torsion return are returns to the conjugate torsion points. -/
theorem norm_orbitPoint_mul_sub_le {μ : ℂ} (hμ : ‖μ‖ = 1) (b : P → ℕ) {t δ : ℝ}
    (hret : ∀ p, ‖orbitPoint P t p - μ ^ b p‖ ≤ δ) (a : ℕ) (p : P) :
    ‖orbitPoint P (a * t) p - torsionPoint (μ ^ a) b p‖ ≤ a * δ := by
  have h1 : ‖orbitPoint P t p‖ ≤ 1 := (norm_phase _ _).le
  have h2 : ‖μ ^ b p‖ ≤ 1 := by rw [norm_pow, hμ, one_pow]
  have h := norm_pow_sub_pow_le h1 h2 a
  have he : orbitPoint P (a * t) p = orbitPoint P t p ^ a := by
    simp only [orbitPoint, phase_nat_mul]
  have he' : torsionPoint (μ ^ a) b p = (μ ^ b p) ^ a := by
    simp only [torsionPoint, ← pow_mul, mul_comm]
  rw [he, he']
  exact h.trans (mul_le_mul_of_nonneg_left (hret p) (Nat.cast_nonneg _))

/-- On a dilate of a torsion return the auxiliary is within `aδ L(F)` of its value at the conjugate
torsion point. -/
theorem norm_aeval_conj_le {μ : ℂ} (hμ : ‖μ‖ = 1) (F : MvPolynomial P ℤ) (b : P → ℕ) {t δ : ℝ}
    (hret : ∀ p, ‖orbitPoint P t p - μ ^ b p‖ ≤ δ) (a : ℕ) :
    ‖MvPolynomial.aeval (torsionPoint (μ ^ a) b) F‖ ≤
      ‖orbitValue F (a * t)‖ + a * δ * lipWeight F := by
  have hu : ∀ p, ‖orbitPoint P (a * t) p‖ ≤ 1 := fun p => (norm_phase _ _).le
  have hv : ∀ p, ‖torsionPoint (μ ^ a) b p‖ ≤ 1 := fun p => by
    rw [torsionPoint, norm_pow, norm_pow, hμ, one_pow, one_pow]
  have h := norm_aeval_sub_le F hu hv (norm_orbitPoint_mul_sub_le hμ b hret a)
  have htri := norm_sub_norm_le (MvPolynomial.aeval (torsionPoint (μ ^ a) b) F)
    (MvPolynomial.aeval (orbitPoint P (a * t)) F)
  rw [norm_sub_rev] at htri
  rw [orbitValue]
  nlinarith

/-- **The norm amplifier on the Frobenius orbit of a torsion return.** If `t` is a `δ`-return to the
torsion point `μ^b` and the product over the dilates `at`, `a < m` prime to `m`, of
`|A(iat)| + aδ L(F)` is below `1`, then `F` vanishes exactly on the closed point `{μ'^b}`. -/
theorem eq_zero_of_small_on_frobeniusOrbit {m : ℕ} (hm : 0 < m) (F : MvPolynomial P ℤ)
    (b : P → ℕ) {μ : ℂ} (hμ : IsPrimitiveRoot μ m) {t δ : ℝ}
    (hret : ∀ p, ‖orbitPoint P t p - μ ^ b p‖ ≤ δ)
    (hsmall : ∏ a ∈ (range m).filter (m.Coprime ·),
      (‖orbitValue F (a * t)‖ + a * δ * lipWeight F) < 1) :
    ∀ μ' ∈ primitiveRoots m ℂ, MvPolynomial.aeval (torsionPoint μ' b) F = 0 := by
  have hμ1 : ‖μ‖ = 1 := hμ.norm'_eq_one hm.ne'
  refine torus_norm_amplifier hm F b ?_
  rw [prod_primitiveRoots_eq hm hμ (fun μ' => ‖MvPolynomial.aeval (torsionPoint μ' b) F‖)]
  refine lt_of_le_of_lt (prod_le_prod (fun _ _ => norm_nonneg _)
    (fun a _ => norm_aeval_conj_le hμ1 F b hret a)) hsmall

/-- **Integer auxiliaries are not small along a Frobenius orbit.** At every `δ`-return to a torsion
point where `F` does not vanish, `Π_a (|A(iat)| + aδ L(F)) ≥ 1` over `a < m` prime to `m`. -/
theorem one_le_prod_frobeniusOrbit {m : ℕ} (hm : 0 < m) (F : MvPolynomial P ℤ) (b : P → ℕ)
    {μ : ℂ} (hμ : IsPrimitiveRoot μ m) {t δ : ℝ}
    (hret : ∀ p, ‖orbitPoint P t p - μ ^ b p‖ ≤ δ)
    (hF : MvPolynomial.aeval (torsionPoint μ b) F ≠ 0) :
    1 ≤ ∏ a ∈ (range m).filter (m.Coprime ·),
      (‖orbitValue F (a * t)‖ + a * δ * lipWeight F) := by
  by_contra h
  exact hF (eq_zero_of_small_on_frobeniusOrbit hm F b hμ hret (not_le.mp h) μ
    ((mem_primitiveRoots hm).mpr hμ))

/-- **Polynomial precision suffices.** If `t` is a `δ`-return to `μ^b` with `mδL(F) ≤ 1/4` and
`|A(iat)| ≤ 1/2` at every dilate `a < m` prime to `m`, then `F` vanishes on the closed point. -/
theorem eq_zero_of_frobeniusOrbit_le_half {m : ℕ} (hm : 0 < m) (F : MvPolynomial P ℤ)
    (b : P → ℕ) {μ : ℂ} (hμ : IsPrimitiveRoot μ m) {t δ : ℝ} (hδ : 0 ≤ δ)
    (hret : ∀ p, ‖orbitPoint P t p - μ ^ b p‖ ≤ δ) (hprec : m * δ * lipWeight F ≤ 1 / 4)
    (hhalf : ∀ a ∈ (range m).filter (m.Coprime ·), ‖orbitValue F (a * t)‖ ≤ 1 / 2) :
    ∀ μ' ∈ primitiveRoots m ℂ, MvPolynomial.aeval (torsionPoint μ' b) F = 0 := by
  refine eq_zero_of_small_on_frobeniusOrbit hm F b hμ hret ?_
  set s := (range m).filter (m.Coprime ·)
  have hne : s.Nonempty := by
    rw [← card_pos, ← Nat.totient_eq_card_coprime]
    exact Nat.totient_pos.mpr hm
  have hfac : ∀ a ∈ s, ‖orbitValue F (a * t)‖ + a * δ * lipWeight F ≤ 3 / 4 := by
    intro a ha
    have ham : (a : ℝ) ≤ m := by
      have := (mem_range.mp (mem_filter.mp ha).1).le
      exact_mod_cast this
    have hL := lipWeight_nonneg F
    have : (a : ℝ) * δ * lipWeight F ≤ m * δ * lipWeight F :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ham hδ) hL
    linarith [hhalf a ha]
  calc ∏ a ∈ s, (‖orbitValue F (a * t)‖ + a * δ * lipWeight F)
      ≤ ∏ _a ∈ s, (3 / 4 : ℝ) :=
        prod_le_prod (fun a _ => add_nonneg (norm_nonneg _)
          (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hδ) (lipWeight_nonneg F))) hfac
    _ = (3 / 4 : ℝ) ^ s.card := prod_const _
    _ ≤ 3 / 4 := pow_le_of_le_one (by norm_num) (by norm_num) (card_pos.mpr hne).ne'
    _ < 1 := by norm_num

end GaloisForLFunctions.ArithmeticLefschetzStepanovTheory
