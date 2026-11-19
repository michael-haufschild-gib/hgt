import GaloisForLFunctions.ArithmeticEffectivityTheory.TheHyperellipticCalibration

/-!
# Integral opposing sections of hyperelliptic point counts

The integral reversed L-polynomial represents inverse Frobenius after
multiplication by its constant coefficient. Combining this representation
with conjugation turns a prescribed positive lag of genuine point-count
traces into a sum of squares of the lower section on the Frobenius roots.
-/

noncomputable section
namespace GaloisForLFunctions.SignedArithmeticCorrespondences
open Finset Polynomial ArithmeticEffectivityTheory ArithmeticCastelnuovoSeveri
open RHTower.Hyperelliptic RHTower.WeilKloosterman
open scoped ComplexConjugate
attribute [local instance] Classical.propDecidable

variable {F : Type*} [Field F] [Fintype F]

/-- Integer lift of the reversed L-polynomial, from its local character sums. -/
def integralFrobeniusPolynomial (f : F[X]) : ℤ[X] :=
  ∑ k ∈ range f.natDegree,
    C (∑ P ∈ monicDeg (F := F) k, quadraticChar F (resultant P f)) * X^(f.natDegree-1-k)

private theorem integralPolynomial_map (f : F[X]) :
    (integralFrobeniusPolynomial f).map (Int.castRingHom ℂ) = lPoly f := by
  classical
  simp [integralFrobeniusPolynomial,lPoly,degSum,degSumW,hypW,Polynomial.map_sum]

private abbrev ev (z : ℂ) : ℤ[X] →+* ℂ := eval₂RingHom (Int.castRingHom ℂ) z

private theorem ev_expansion (P : ℤ[X]) (z : ℂ) :
    ev z P = ∑ j ∈ P.support, (P.coeff j:ℂ)*z^j := by
  change P.eval₂ (Int.castRingHom ℂ) z = _
  rw [eval₂_eq_sum]
  rfl

private theorem ev_C (z : ℂ) (c : ℤ) : ev z (C c) = (c:ℂ) := eval₂_C ..

private theorem ev_X (z : ℂ) : ev z X = z := eval₂_X ..

/-- The clearing factor is nonzero on every smooth odd-degree curve,
including the case of an empty spectrum. -/
theorem integralFrobeniusPolynomial_constant_ne_zero (hF : ringChar F ≠ 2) {f : F[X]}
    (hsq : Squarefree f) (hodd : Odd f.natDegree) : (integralFrobeniusPolynomial f).coeff 0≠0 := by
  intro he
  have hz : (0:ℂ)∈lRoots f := by
    apply (mem_roots (lPoly_monic f hodd.pos).ne_zero).mpr
    rw [IsRoot,← coeff_zero_eq_eval_zero,← integralPolynomial_map,coeff_map,he,map_zero]
  have hn := (riemannHypothesis_oddHyperelliptic.{_,0} hF hsq hodd).2.1 0 hz
  exact (Real.sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)).ne' (by simpa using hn.symm)

private theorem root_evaluates_zero {f : F[X]} (i : Fin (lRoots f).toList.length) :
    ev (rootEnum (lRoots f) i) (integralFrobeniusPolynomial f) = 0 := by
  change (integralFrobeniusPolynomial f).eval₂ _ _ = _
  rw [← eval_map,integralPolynomial_map]
  exact isRoot_of_mem_roots (rootEnum_mem _ i)

/-- Integral polynomial opposing an arbitrary integral section at lag L.
The first factor clears the scale, the second cancels the lag, and the
reversed section evaluates to a power of Frobenius times the conjugate. -/
def opposingFrobeniusSection (q L : ℕ) (A P : ℤ[X]) : ℤ[X] :=
  C (A.coeff 0)^(L+P.natDegree) * (-A.divX)^(L+P.natDegree) *
    ∑ j ∈ P.support, C (P.coeff j*(q:ℤ)^j)*X^(P.natDegree-j)

/-- At an individual Weil root the opposing section implements complex
conjugation and cancels the prescribed positive Frobenius lag. -/
theorem opposingFrobeniusSection_eval {A P : ℤ[X]} {q : ℕ} {z : ℂ}
    (hz : A.eval₂ (Int.castRingHom ℂ) z=0) (hq : z*conj z=(q:ℂ)) (L : ℕ) :
    z^L*P.eval₂ (Int.castRingHom ℂ) z*
      (opposingFrobeniusSection q L A P).eval₂ (Int.castRingHom ℂ) z =
      (((A.coeff 0:ℤ):ℂ)^(L+P.natDegree))^2 * (‖P.eval₂ (Int.castRingHom ℂ) z‖:ℂ)^2 := by
  change ev z A=0 at hz
  let m := P.natDegree
  let c : ℂ := A.coeff 0
  let s := ev z (-A.divX)
  have hsc : z*s=c := by
    have he := congrArg (ev z) (X_mul_divX_add A)
    simp only [map_add,map_mul,ev_X,ev_C,hz] at he
    dsimp only [s,c]
    rw [map_neg,mul_neg]
    exact neg_eq_of_add_eq_zero_left he
  have hv : ev z (∑ j ∈ P.support, C (P.coeff j*(q:ℤ)^j)*X^(m-j)) = z^m*conj (ev z P) := by
    simp only [map_sum,map_mul,ev_C,map_pow,ev_X,Int.cast_mul,Int.cast_pow,Int.cast_natCast,
      ev_expansion P z,map_intCast,mul_sum]
    refine sum_congr rfl fun j hj => ?_
    have hjm := le_natDegree_of_ne_zero (mem_support_iff.mp hj)
    rw [← hq,mul_pow]
    rw [show z^m = z^j*z^(m-j) by rw [← pow_add]; congr 1; omega]
    ring
  change z^L*ev z P*ev z (C (A.coeff 0)^(L+m)*(-A.divX)^(L+m)*_) = _
  rw [map_mul,map_mul,map_pow,map_pow,ev_C,hv]
  change z^L*ev z P*(c^(L+m)*s^(L+m)*(z^m*conj (ev z P))) = (c^(L+m))^2*_
  calc _ = c^(L+m)*(z*s)^(L+m)*(ev z P*conj (ev z P)) := by rw [mul_pow,pow_add z]; ring
       _ = _ := by rw [hsc,Complex.mul_conj']; ring

/-- Pole-subtracted mixed trace in strictly positive extension degrees.
Every entry of pointCount is the affine point cardinality plus infinity. -/
def curveCountPair (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hodd : Odd f.natDegree) (L : ℕ+) (P Q : ℤ[X]) : ℝ :=
  let D := hyperellipticDatum hF hsq hodd
  ∑ j ∈ P.support, ∑ k ∈ Q.support, (P.coeff j:ℝ)*Q.coeff k*
    ((Fintype.card F:ℝ)^((L:ℕ)+j+k)+1-D.pointCount ((L:ℕ)+j+k))

private theorem ghost_sum (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hodd : Odd f.natDegree) (n : ℕ) :
    (((Fintype.card F:ℝ)^n+1-(hyperellipticDatum hF hsq hodd).pointCount n:ℝ):ℂ) =
      ∑ i, rootEnum (lRoots f) i ^ n := by
  let D := hyperellipticDatum hF hsq hodd
  have hq : D.q=Fintype.card F := rfl
  have hroot (i) : (D.sqrtq:ℂ)*D.β i=rootEnum (lRoots f) i := by
    change (Real.sqrt (Fintype.card F):ℂ)*(rootEnum (lRoots f) i/(Real.sqrt (Fintype.card F):ℂ))=_
    exact mul_div_cancel₀ _ sqrt_card_ne_zero
  calc _ = (D.sqrtq:ℂ)^n*D.powerSum n := by
         rw [D.powerSum_eq_trace,← Complex.ofReal_pow,← Complex.ofReal_mul]
         congr 1
         change _+1-D.pointCount n=_
         rw [CurveDatum.pointCount,hq]
         ring
       _ = _ := by
         rw [CurveDatum.powerSum,mul_sum]
         exact sum_congr rfl fun i _ => by rw [← mul_pow,hroot]

private theorem curveCountPair_spectral (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hodd : Odd f.natDegree) (L : ℕ+) (P Q : ℤ[X]) :
    (curveCountPair hF hsq hodd L P Q:ℂ) = ∑ i,
      (rootEnum (lRoots f) i)^(L:ℕ)*ev (rootEnum (lRoots f) i) P*ev (rootEnum (lRoots f) i) Q := by
  let z := rootEnum (lRoots f)
  have reorder (H : ℕ → ℕ → Fin (lRoots f).toList.length → ℂ) :
      (∑ j ∈ P.support, ∑ k ∈ Q.support, ∑ i, H j k i) =
        ∑ i, ∑ j ∈ P.support, ∑ k ∈ Q.support, H j k i := by
    calc _ = ∑ j ∈ P.support, ∑ i, ∑ k ∈ Q.support, H j k i :=
           sum_congr rfl fun j _ => sum_comm
         _ = _ := sum_comm
  simp only [curveCountPair,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_intCast,
    ghost_sum hF hsq hodd,mul_sum]
  rw [reorder]
  refine sum_congr rfl fun i _ => ?_
  rw [ev_expansion,ev_expansion,mul_assoc ((z i)^(L:ℕ)),sum_mul_sum]
  simp only [mul_sum]
  refine sum_congr rfl fun j _ => sum_congr rfl fun k _ => ?_
  simp only [pow_add]
  ring

/-- For every odd-degree squarefree curve in odd characteristic, a single
integral opposing section at each prescribed lag recovers precisely the
sum of squared section values over the actual Frobenius spectrum. -/
theorem hyperelliptic_opposing_square (hF : ringChar F ≠ 2) {f : F[X]} (hsq : Squarefree f)
    (hodd : Odd f.natDegree) (L : ℕ+) (P : ℤ[X]) :
    let A := integralFrobeniusPolynomial f
    curveCountPair hF hsq hodd L P (opposingFrobeniusSection (Fintype.card F) L A P) =
      ((A.coeff 0:ℝ)^((L:ℕ)+P.natDegree))^2 *
        ∑ i, ‖P.eval₂ (Int.castRingHom ℂ) (rootEnum (lRoots f) i)‖^2 := by
  intro A
  apply Complex.ofReal_injective
  rw [curveCountPair_spectral,Complex.ofReal_mul,Complex.ofReal_sum,mul_sum]
  refine sum_congr rfl fun i _ => ?_
  let z := rootEnum (lRoots f) i
  have hq : z*conj z=(Fintype.card F:ℂ) := by
    rw [Complex.mul_conj',← Complex.ofReal_pow,norm_rootEnum_eq hF hsq hodd i,
      Real.sq_sqrt (Nat.cast_nonneg _),Complex.ofReal_natCast]
  simpa only [Complex.ofReal_pow,Complex.ofReal_intCast] using
    opposingFrobeniusSection_eval (P := P) (root_evaluates_zero i) hq (L:ℕ)

/-- At each extension degree the measured trace is obtained by counting
the points on the affine equation, with the rational point at infinity
cancelling the constant pole. -/
theorem curveCountPair_trace_counts (hF : ringChar F ≠ 2) {f : F[X]}
    (hsq : Squarefree f) (hodd : Odd f.natDegree) (E : Type*) [Field E] [Fintype E] [Algebra F E] :
    (Fintype.card F:ℝ)^(Module.finrank F E)+1-
      (hyperellipticDatum hF hsq hodd).pointCount (Module.finrank F E) =
      (Fintype.card F:ℝ)^(Module.finrank F E)-
        ((univ.filter fun xy : E×E => xy.2^2=aeval xy.1 f).card:ℝ) := by
  rw [hyperellipticDatum_pointCount hF hsq hodd E]
  ring

/-- The nullspace consists exactly of sections vanishing on every
Frobenius root. Repeated roots are counted with their multiplicity. -/
theorem hyperelliptic_opposing_nullspace (hF : ringChar F ≠ 2) {f : F[X]}
    (hsq : Squarefree f) (hodd : Odd f.natDegree) (L : ℕ+) (P : ℤ[X]) :
    curveCountPair hF hsq hodd L P
        (opposingFrobeniusSection (Fintype.card F) L (integralFrobeniusPolynomial f) P) = 0 ↔
      ∀ i, P.eval₂ (Int.castRingHom ℂ) (rootEnum (lRoots f) i)=0 := by
  rw [hyperelliptic_opposing_square]
  have ha : ((integralFrobeniusPolynomial f).coeff 0:ℝ) ≠ 0 :=
    Int.cast_ne_zero.mpr (integralFrobeniusPolynomial_constant_ne_zero hF hsq hodd)
  rw [mul_eq_zero,or_iff_right (pow_ne_zero _ (pow_ne_zero _ ha)),
    sum_eq_zero_iff_of_nonneg (fun _ _ => sq_nonneg _)]
  simp

#print axioms integralFrobeniusPolynomial_constant_ne_zero
#print axioms opposingFrobeniusSection_eval
#print axioms curveCountPair_trace_counts
#print axioms hyperelliptic_opposing_square
#print axioms hyperelliptic_opposing_nullspace
end GaloisForLFunctions.SignedArithmeticCorrespondences
