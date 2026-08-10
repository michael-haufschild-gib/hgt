import GaloisForLFunctions.HTGeometry.HenselFactorization
import GaloisForLFunctions.HTGeometry.PowerSeriesRootLift

/-!
# Coprime factorisations of the special fibre lift to power series

A polynomial over `K⟦t⟧` whose reduction at `t = 0` splits into coprime factors, one of them monic,
splits the same way over `K⟦t⟧` itself.  This is Hensel's lemma for the variable ideal, and it is
the step that turns a Newton polygon into a factorisation: the edge polynomial's distinct roots
separate the fibre, and the separation propagates to the whole power-series family.

The reduction map is `Polynomial.map` along `PowerSeries.constantCoeff`, and the lift is
`Polynomial.map` along `PowerSeries.C`; the two compose to the identity, which is what turns the
Bézout identity of the fibre into the invertibility hypothesis of Hensel's lemma.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial PowerSeries

variable {K : Type} [Field K]

/-- Coefficientwise membership in the variable ideal is vanishing of the reduction. -/
theorem coeffMem_span_X_iff {p : (PowerSeries K)[X]} :
    CoeffMem (Ideal.span {(PowerSeries.X : PowerSeries K)}) p ↔
      p.map (PowerSeries.constantCoeff (R := K)) = 0 := by
  constructor
  · intro h
    ext i
    rw [Polynomial.coeff_map, Polynomial.coeff_zero]
    exact mem_span_X_iff.mp (h i)
  · intro h i
    rw [mem_span_X_iff]
    have hi := congrArg (fun q => Polynomial.coeff q i) h
    simpa using hi

/-- Reduction undoes the constant lift. -/
theorem map_constantCoeff_map_C (p : K[X]) :
    (p.map (PowerSeries.C (R := K))).map (PowerSeries.constantCoeff (R := K)) = p := by
  have hcomp : (PowerSeries.constantCoeff (R := K)).comp (PowerSeries.C (R := K))
      = RingHom.id K := by
    ext a
    simp
  rw [Polynomial.map_map, hcomp, Polynomial.map_id]

/-- **A coprime factorisation of the fibre lifts.**  If the reduction of `f` at `t = 0` factors as
`a * b` with `a` monic and `a`, `b` coprime, then `f` itself factors accordingly. -/
theorem exists_factorization_of_coprime_reduction {f : (PowerSeries K)[X]} {a b : K[X]}
    (ha : a.Monic) (hred : f.map (PowerSeries.constantCoeff (R := K)) = a * b)
    (hcop : IsCoprime a b) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧ g.degree = a.degree ∧ f = g * h ∧
      g.map (PowerSeries.constantCoeff (R := K)) = a ∧
      h.map (PowerSeries.constantCoeff (R := K)) = b := by
  classical
  obtain ⟨u, v, huv⟩ := hcop
  have hg₀ : (a.map (PowerSeries.C (R := K))).Monic := ha.map _
  have happrox : CoeffMem (Ideal.span {(PowerSeries.X : PowerSeries K)})
      (f - a.map (PowerSeries.C (R := K)) * b.map (PowerSeries.C (R := K))) := by
    rw [coeffMem_span_X_iff, Polynomial.map_sub, Polynomial.map_mul, map_constantCoeff_map_C,
      map_constantCoeff_map_C, hred, sub_self]
  have hbez : CoeffMem (Ideal.span {(PowerSeries.X : PowerSeries K)})
      (v.map (PowerSeries.C (R := K)) * b.map (PowerSeries.C (R := K))
        + u.map (PowerSeries.C (R := K)) * a.map (PowerSeries.C (R := K)) - 1) := by
    rw [coeffMem_span_X_iff, Polynomial.map_sub, Polynomial.map_add, Polynomial.map_mul,
      Polynomial.map_mul, map_constantCoeff_map_C, map_constantCoeff_map_C,
      map_constantCoeff_map_C, map_constantCoeff_map_C, Polynomial.map_one, huv, sub_self]
  obtain ⟨g, h, hgm, hgdeg, hfgh, hgsub, hhsub⟩ :=
    exists_monic_factorization (Ideal.span {(PowerSeries.X : PowerSeries K)}) hg₀ happrox hbez
  have hCinj : Function.Injective (PowerSeries.C (R := K)) := (PowerSeries.C (R := K)).injective
  refine ⟨g, h, hgm, ?_, hfgh, ?_, ?_⟩
  · rw [hgdeg, Polynomial.degree_map_eq_of_injective hCinj]
  · have hz := coeffMem_span_X_iff.mp hgsub
    rw [Polynomial.map_sub, sub_eq_zero, map_constantCoeff_map_C] at hz
    exact hz
  · have hz := coeffMem_span_X_iff.mp hhsub
    rw [Polynomial.map_sub, sub_eq_zero, map_constantCoeff_map_C] at hz
    exact hz

/-- **A root of the fibre of multiplicity below the degree splits off a proper monic factor.**
The factor has the multiplicity as its degree, so a Newton-polygon edge with two distinct roots
always produces a factorisation into strictly smaller monic pieces. -/
theorem exists_monic_factor_of_rootMultiplicity {f : (PowerSeries K)[X]} (hf : f.Monic) (c : K) :
    ∃ g h : (PowerSeries K)[X], g.Monic ∧
      g.natDegree = (f.map (PowerSeries.constantCoeff (R := K))).rootMultiplicity c ∧
      f = g * h := by
  classical
  set F : K[X] := f.map (PowerSeries.constantCoeff (R := K)) with hFdef
  have hFmonic : F.Monic := hf.map _
  have hFne : F ≠ 0 := hFmonic.ne_zero
  set m : ℕ := F.rootMultiplicity c with hmdef
  set b : K[X] := F /ₘ (X - Polynomial.C c) ^ m with hbdef
  have hdvd : ((X : K[X]) - Polynomial.C c) ^ m ∣ F := pow_rootMultiplicity_dvd F c
  have hmonicpow : (((X : K[X]) - Polynomial.C c) ^ m).Monic := (monic_X_sub_C c).pow m
  have hFfact : F = ((X : K[X]) - Polynomial.C c) ^ m * b := by
    rw [hbdef, Polynomial.mul_divByMonic_cancel_left]
    · exact (Polynomial.modByMonic_eq_zero_iff_dvd hmonicpow).mp
        ((Polynomial.modByMonic_eq_zero_iff_dvd hmonicpow).mpr hdvd) ▸ rfl
    · exact hmonicpow
  sorry

end GaloisForLFunctions.HTGeometry
