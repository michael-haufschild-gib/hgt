import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflected6

/-!
# Exact reflected compact source jet of order 8

Complex source incidence is normalized separately from the real polynomial
identity. One derivative order per module keeps transient proof state bounded.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Exact scalar polynomial for the reflected source jet of order 8. -/
def oddCompactReflectedScalar8 (u a w : ℝ) : ℝ :=
  (((((((1207665 / 64 : ℝ) +
    (-2122095 / 32 : ℝ)*a^(1 : ℕ)) +
    ((2892639 / 32 : ℝ)*a^(1 : ℕ)*w^(2 : ℕ) +
    ((-77553 / 4 : ℝ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (3993 / 4 : ℝ)*a^(1 : ℕ)*w^(6 : ℕ)))) +
    (((-12 / 1 : ℝ)*a^(1 : ℕ)*w^(8 : ℕ) +
    ((16407993 / 512 : ℝ)*a^(2 : ℕ) +
    (-191961 / 64 : ℝ)*a^(2 : ℕ)*w^(2 : ℕ))) +
    ((-31179 / 64 : ℝ)*a^(2 : ℕ)*w^(4 : ℕ) +
    ((39 / 2 : ℝ)*a^(2 : ℕ)*w^(6 : ℕ) +
    (1024127 / 1024 : ℝ)*a^(3 : ℕ))))) +
    ((((226287 / 512 : ℝ)*a^(3 : ℕ)*w^(2 : ℕ) +
    ((-1911 / 64 : ℝ)*a^(3 : ℕ)*w^(4 : ℕ) +
    (3 / 16 : ℝ)*a^(3 : ℕ)*w^(6 : ℕ))) +
    ((7963857 / 16384 : ℝ)*a^(4 : ℕ) +
    ((-6591 / 256 : ℝ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-105 / 256 : ℝ)*a^(4 : ℕ)*w^(4 : ℕ)))) +
    (((-30027 / 16384 : ℝ)*a^(5 : ℕ) +
    ((2595 / 2048 : ℝ)*a^(5 : ℕ)*w^(2 : ℕ) +
    (5133 / 65536 : ℝ)*a^(6 : ℕ))) +
    ((-12127 / 16 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    ((21084 / 1 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-3462 / 1 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)))))) +
    (((((86 / 1 : ℝ)*u^(1 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    ((100249 / 48 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (10795 / 4 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ))) +
    ((-757 / 4 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    ((1 / 1 : ℝ)*u^(1 : ℕ)*a^(2 : ℕ)*w^(7 : ℕ) +
    (308085 / 256 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ)))) +
    (((11919 / 64 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ) +
    ((-7 / 2 : ℝ)*u^(1 : ℕ)*a^(3 : ℕ)*w^(5 : ℕ) +
    (62221 / 512 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ))) +
    ((627 / 128 : ℝ)*u^(1 : ℕ)*a^(4 : ℕ)*w^(3 : ℕ) +
    ((397 / 1024 : ℝ)*u^(1 : ℕ)*a^(5 : ℕ)*w^(1 : ℕ) +
    (-500055 / 32 : ℝ)*u^(2 : ℕ))))) +
    ((((1228535 / 48 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ) +
    ((-126433 / 6 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    (25577 / 4 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ))) +
    ((-2059 / 6 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ) +
    ((4 / 3 : ℝ)*u^(2 : ℕ)*a^(1 : ℕ)*w^(8 : ℕ) +
    (-3465835 / 576 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)))) +
    (((57633 / 64 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    ((53609 / 96 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ) +
    (-10 / 1 : ℝ)*u^(2 : ℕ)*a^(2 : ℕ)*w^(6 : ℕ))) +
    ((1245229 / 1024 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ) +
    ((-71 / 256 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (3793 / 192 : ℝ)*u^(2 : ℕ)*a^(3 : ℕ)*w^(4 : ℕ))))))) +
    ((((((-1082891 / 24576 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ) +
    ((179 / 64 : ℝ)*u^(2 : ℕ)*a^(4 : ℕ)*w^(2 : ℕ) +
    (-3165 / 16384 : ℝ)*u^(2 : ℕ)*a^(5 : ℕ))) +
    ((-77351 / 36 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    ((-57593 / 18 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (5720 / 9 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ)))) +
    (((-86 / 9 : ℝ)*u^(3 : ℕ)*a^(1 : ℕ)*w^(7 : ℕ) +
    ((40807 / 36 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    (-1991 / 6 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ))) +
    ((1309 / 36 : ℝ)*u^(3 : ℕ)*a^(2 : ℕ)*w^(5 : ℕ) +
    ((198065 / 1152 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ) +
    (-8711 / 576 : ℝ)*u^(3 : ℕ)*a^(3 : ℕ)*w^(3 : ℕ))))) +
    ((((-3557 / 4608 : ℝ)*u^(3 : ℕ)*a^(4 : ℕ)*w^(1 : ℕ) +
    ((1007365 / 192 : ℝ)*u^(4 : ℕ) +
    (-79083 / 16 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ))) +
    ((168215 / 144 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    ((-58885 / 108 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    (929 / 36 : ℝ)*u^(4 : ℕ)*a^(1 : ℕ)*w^(6 : ℕ)))) +
    (((8431439 / 6912 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ) +
    ((188467 / 1728 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ) +
    (-19795 / 576 : ℝ)*u^(4 : ℕ)*a^(2 : ℕ)*w^(4 : ℕ))) +
    ((-289477 / 3072 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ) +
    ((236581 / 13824 : ℝ)*u^(4 : ℕ)*a^(3 : ℕ)*w^(2 : ℕ) +
    (-32471 / 147456 : ℝ)*u^(4 : ℕ)*a^(4 : ℕ)))))) +
    (((((50129 / 216 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    ((4267 / 81 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ) +
    (-2258 / 81 : ℝ)*u^(5 : ℕ)*a^(1 : ℕ)*w^(5 : ℕ))) +
    ((87587 / 1296 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    ((1885 / 108 : ℝ)*u^(5 : ℕ)*a^(2 : ℕ)*w^(3 : ℕ) +
    (-131959 / 20736 : ℝ)*u^(5 : ℕ)*a^(3 : ℕ)*w^(1 : ℕ)))) +
    (((-1192825 / 1296 : ℝ)*u^(6 : ℕ) +
    ((1060831 / 1944 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ) +
    (6233 / 972 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ))) +
    ((8005 / 972 : ℝ)*u^(6 : ℕ)*a^(1 : ℕ)*w^(4 : ℕ) +
    ((-607003 / 7776 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ) +
    (94973 / 15552 : ℝ)*u^(6 : ℕ)*a^(2 : ℕ)*w^(2 : ℕ))))) +
    ((((230545 / 248832 : ℝ)*u^(6 : ℕ)*a^(3 : ℕ) +
    ((32729 / 2916 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ) +
    (2297 / 486 : ℝ)*u^(7 : ℕ)*a^(1 : ℕ)*w^(3 : ℕ))) +
    ((-28745 / 5832 : ℝ)*u^(7 : ℕ)*a^(2 : ℕ)*w^(1 : ℕ) +
    ((463295 / 5184 : ℝ)*u^(8 : ℕ) +
    (-2110465 / 69984 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)))) +
    (((-439 / 69984 : ℝ)*u^(8 : ℕ)*a^(1 : ℕ)*w^(2 : ℕ) +
    ((497773 / 373248 : ℝ)*u^(8 : ℕ)*a^(2 : ℕ) +
    (-110159 / 104976 : ℝ)*u^(9 : ℕ)*a^(1 : ℕ)*w^(1 : ℕ))) +
    ((-35525 / 7776 : ℝ)*u^(10 : ℕ) +
    ((21551 / 34992 : ℝ)*u^(10 : ℕ)*a^(1 : ℕ) +
    (13475 / 139968 : ℝ)*u^(12 : ℕ))))))))

/-- Symbolic normalization of the reflected jet before determinant formation. -/
theorem oddCompactReflectedScalar8_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w) (oddCompactReflectedJetPolynomial 8) =
      (oddCompactReflectedScalar8 u a w : ℂ) := by
  have hf : MvPolynomial.eval (oddCompactState u a w)
      (oddCompactReflectedJetPolynomial 8) =
      ((((((1 : ℝ)*oddCompactSourceScalar0 u a w*oddCompactSourceScalar8 u a w +
    (-8 : ℝ)*oddCompactSourceScalar1 u a w*oddCompactSourceScalar7 u a w) +
    ((28 : ℝ)*oddCompactSourceScalar2 u a w*oddCompactSourceScalar6 u a w +
    (-56 : ℝ)*oddCompactSourceScalar3 u a w*oddCompactSourceScalar5 u a w)) +
    (((70 : ℝ)*oddCompactSourceScalar4 u a w*oddCompactSourceScalar4 u a w +
    (-56 : ℝ)*oddCompactSourceScalar5 u a w*oddCompactSourceScalar3 u a w) +
    ((28 : ℝ)*oddCompactSourceScalar6 u a w*oddCompactSourceScalar2 u a w +
    ((-8 : ℝ)*oddCompactSourceScalar7 u a w*oddCompactSourceScalar1 u a w +
    (1 : ℝ)*oddCompactSourceScalar8 u a w*oddCompactSourceScalar0 u a w)))) : ℝ) : ℂ) := by
    rw [eval_oddCompactReflectedJetPolynomial]
    norm_num only [Finset.sum_range_succ, Finset.sum_empty, Nat.choose, Nat.reduceSub, Nat.reduceAdd]
    simp only [oddCompactSourceScalar0_eq, oddCompactSourceScalar1_eq, oddCompactSourceScalar2_eq, oddCompactSourceScalar3_eq, oddCompactSourceScalar4_eq, oddCompactSourceScalar5_eq, oddCompactSourceScalar6_eq, oddCompactSourceScalar7_eq, oddCompactSourceScalar8_eq]
    push_cast
    ring
  rw [hf]
  apply congrArg Complex.ofReal
  unfold oddCompactSourceScalar0 oddCompactSourceScalar1 oddCompactSourceScalar2 oddCompactSourceScalar3 oddCompactSourceScalar4 oddCompactSourceScalar5 oddCompactSourceScalar6 oddCompactSourceScalar7 oddCompactSourceScalar8 oddCompactReflectedScalar8
  ring


end
end HTGeometry
