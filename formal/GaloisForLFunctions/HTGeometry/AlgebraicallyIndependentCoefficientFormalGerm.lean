import GaloisForLFunctions.HTGeometry.GenericJetInjectivity

/-!
# Formal hypertranscendence from algebraically independent coefficients

The power series with universal coefficients `X₀, X₁, ...` is formally
hypertranscendental: a nonzero differential polynomial cannot vanish after its jet
substitution.  Indeed, every scalar power series is a specialization of the universal one,
so a universal vanishing identity would contradict `formalJets_substitution_injective`.

Consequently, any power series whose coefficient family is algebraically independent over
`ℂ` is formally hypertranscendental.  This converts coefficient-sequence freeness into the
exact all-order jet-separation statement needed by the Gamma factorial pole germ.
-/

open PowerSeries MvPolynomial

namespace GaloisForLFunctions

noncomputable section

/-- Formal point-and-derivative jets over an arbitrary coefficient semiring. -/
def formalJetsOver {R : Type*} [CommSemiring R]
    (n : ℕ) (F : R⟦X⟧) : Fin (n + 2) → R⟦X⟧ :=
  Fin.cons PowerSeries.X
    (fun j : Fin (n + 1) => (⇑(d⁄dX R))^[(j : ℕ)] F)

/-- Mapping coefficients commutes with formal differentiation. -/
theorem map_powerSeriesDerivative
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (F : R⟦X⟧) :
    PowerSeries.map f (d⁄dX R F) =
      d⁄dX S (PowerSeries.map f F) := by
  ext n
  rw [PowerSeries.coeff_map, PowerSeries.coeff_derivative,
    PowerSeries.coeff_derivative, PowerSeries.coeff_map]
  simp

/-- Mapping coefficients commutes with every iterated formal derivative. -/
theorem map_iterate_powerSeriesDerivative
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (F : R⟦X⟧) (j : ℕ) :
    PowerSeries.map f ((⇑(d⁄dX R))^[j] F) =
      (⇑(d⁄dX S))^[j] (PowerSeries.map f F) := by
  induction j with
  | zero => simp
  | succ j ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
        map_powerSeriesDerivative, ih]

/-- The complete finite jet vector is natural under coefficient maps. -/
theorem map_formalJetsOver
    {R S : Type*} [CommSemiring R] [CommSemiring S]
    (f : R →+* S) (n : ℕ) (F : R⟦X⟧) :
    (fun i => PowerSeries.map f (formalJetsOver n F i)) =
      formalJetsOver n (PowerSeries.map f F) := by
  funext i
  induction i using Fin.cases with
  | zero => simp [formalJetsOver]
  | succ j => simp [formalJetsOver, map_iterate_powerSeriesDerivative]

/-- Differential-polynomial evaluation is natural under coefficient-algebra maps. -/
theorem map_aeval_powerSeries
    {A B σ : Type*} [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] (f : A →ₐ[ℂ] B)
    (g : σ → A⟦X⟧) (P : MvPolynomial σ ℂ) :
    PowerSeries.mapAlgHom f (MvPolynomial.aeval g P) =
      MvPolynomial.aeval (fun i => PowerSeries.mapAlgHom f (g i)) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp
  | add P Q hP hQ => simpa using congrArg₂ (· + ·) hP hQ
  | mul_X P i hP => simp [hP]

/-- The universal scalar power series `Σ Xₖ Tᵏ`. -/
def genericCoefficientPowerSeries : (MvPolynomial ℕ ℂ)⟦X⟧ :=
  PowerSeries.mk fun k => MvPolynomial.X k

/-- Specializing the universal coefficients produces the prescribed power series. -/
theorem map_genericCoefficientPowerSeries
    {A : Type*} [CommRing A] [Algebra ℂ A] (a : ℕ → A) :
    PowerSeries.map (MvPolynomial.aeval a).toRingHom
        genericCoefficientPowerSeries =
      PowerSeries.mk a := by
  ext k
  simp [genericCoefficientPowerSeries]

/-- **Universal formal-germ separation.**  Every nonzero differential polynomial survives
substitution of the universal-coefficient power series and its finite jet. -/
theorem aeval_genericFormalJets_ne_zero {n : ℕ}
    {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    MvPolynomial.aeval
      (formalJetsOver n genericCoefficientPowerSeries) P ≠ 0 := by
  intro hzero
  apply hP
  apply formalJets_substitution_injective
  intro G
  let f : MvPolynomial ℕ ℂ →ₐ[ℂ] ℂ :=
    MvPolynomial.aeval (fun k => PowerSeries.coeff k G)
  have hmap := congrArg (PowerSeries.mapAlgHom f) hzero
  rw [map_zero] at hmap
  rw [map_aeval_powerSeries] at hmap
  have hgen : PowerSeries.map f.toRingHom genericCoefficientPowerSeries = G := by
    rw [show G = PowerSeries.mk (fun k => PowerSeries.coeff k G) from by
      ext k
      simp]
    exact map_genericCoefficientPowerSeries _
  have hjets :
      (fun i => PowerSeries.mapAlgHom f
        (formalJetsOver n genericCoefficientPowerSeries i)) =
        formalJetsOver n G := by
    simpa only [PowerSeries.mapAlgHom_apply, hgen] using
      map_formalJetsOver f.toRingHom n genericCoefficientPowerSeries
  rw [hjets] at hmap
  simpa [formalJetsOver, formalJets] using hmap

/-- **Algebraically independent coefficients force formal hypertranscendence.**
If `a₀, a₁, ...` are algebraically independent over `ℂ`, then `Σ aₖ Tᵏ`
satisfies no nonzero finite-order algebraic differential equation over `ℂ[T]`. -/
theorem aeval_formalJetsOver_ne_zero_of_coeff_algebraicIndependent
    {A : Type*} [CommRing A] [Algebra ℂ A]
    (a : ℕ → A) (ha : AlgebraicIndependent ℂ a) {n : ℕ}
    {P : MvPolynomial (Fin (n + 2)) ℂ} (hP : P ≠ 0) :
    MvPolynomial.aeval (formalJetsOver n (PowerSeries.mk a)) P ≠ 0 := by
  let U : (MvPolynomial ℕ ℂ)⟦X⟧ :=
    MvPolynomial.aeval
      (formalJetsOver n genericCoefficientPowerSeries) P
  have hU : U ≠ 0 := aeval_genericFormalJets_ne_zero hP
  obtain ⟨N, hN⟩ : ∃ N, PowerSeries.coeff N U ≠ 0 := by
    by_contra h
    push Not at h
    apply hU
    apply PowerSeries.ext
    intro N
    exact h N
  let f : MvPolynomial ℕ ℂ →ₐ[ℂ] A := MvPolynomial.aeval a
  have hf : Function.Injective f :=
    algebraicIndependent_iff_injective_aeval.mp ha
  intro hzero
  have hnat : PowerSeries.mapAlgHom f U =
      MvPolynomial.aeval (formalJetsOver n (PowerSeries.mk a)) P := by
    rw [show U = MvPolynomial.aeval
      (formalJetsOver n genericCoefficientPowerSeries) P from rfl,
      map_aeval_powerSeries]
    have hgen : PowerSeries.map f.toRingHom genericCoefficientPowerSeries =
        PowerSeries.mk a := by
      simpa [f] using map_genericCoefficientPowerSeries a
    have hjets :
        (fun i => PowerSeries.mapAlgHom f
          (formalJetsOver n genericCoefficientPowerSeries i)) =
          formalJetsOver n (PowerSeries.mk a) := by
      simpa only [PowerSeries.mapAlgHom_apply, hgen] using
        map_formalJetsOver f.toRingHom n genericCoefficientPowerSeries
    rw [hjets]
  have hmap : PowerSeries.mapAlgHom f U = 0 := hnat.trans hzero
  have hc := congrArg (PowerSeries.coeff N) hmap
  simp only [PowerSeries.mapAlgHom_apply, PowerSeries.coeff_map, map_zero] at hc
  have hz : PowerSeries.coeff N U = 0 := hf (by simpa using hc)
  exact hN hz

end

end GaloisForLFunctions
