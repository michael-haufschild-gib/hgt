import GaloisForLFunctions.HTGeometry.Octonion.Basic

namespace GaloisForLFunctions.HTGeometry.Octonion.RealOctonion

noncomputable section

/-- Two copies of the one-dimensional octonion module. -/
structure TwoOctonions where
  first : RealOctonion
  second : RealOctonion

@[ext] theorem TwoOctonions.ext {x y : TwoOctonions}
    (hfirst : x.first = y.first) (hsecond : x.second = y.second) : x = y := by
  cases x
  cases y
  cases hfirst
  cases hsecond
  rfl

/-- The two-block real resolvent from Example 8.10. -/
def twoBlockResolvent (s e : RealOctonion) : TwoOctonions → TwoOctonions := fun x =>
  ⟨x.first * s + e * x.second, star e * x.first + x.second * s⟩

/-- The triangular right factor in paper equation (8.10). -/
def twoBlockResolventShear (s e : RealOctonion) : TwoOctonions → TwoOctonions := fun x =>
  ⟨x.first - (e * x.second) * inverse s, x.second⟩

/-- The Schur-factorized operator in paper equation (8.10). -/
def twoBlockResolventSchurFactor (s e : RealOctonion) :
    TwoOctonions → TwoOctonions := fun x =>
  ⟨x.first * s,
    star e * x.first + x.second * s - star e * ((e * x.second) * inverse s)⟩

/-- Paper equation (8.10), in closed two-block operator form. -/
theorem twoBlockResolvent_factorization
    (s e : RealOctonion) (hs : s ≠ 0) :
    twoBlockResolvent s e ∘ twoBlockResolventShear s e =
      twoBlockResolventSchurFactor s e := by
  funext x
  apply TwoOctonions.ext
  · unfold Function.comp twoBlockResolvent twoBlockResolventShear twoBlockResolventSchurFactor
    rw [sub_mul, mul_inverse_mul s (e * x.second) hs]
    abel_nf
  · unfold Function.comp twoBlockResolvent twoBlockResolventShear twoBlockResolventSchurFactor
    rw [mul_sub]
    abel_nf

end
end GaloisForLFunctions.HTGeometry.Octonion.RealOctonion
