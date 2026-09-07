import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflected8

/-!
# Exact reflected compact source jet of order 10

Complex source incidence is normalized separately from the real polynomial
identity. One derivative order per module keeps transient proof state bounded.
-/

namespace HTGeometry
noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Exact scalar polynomial for the reflected source jet of order 10. -/
def oddCompactReflectedScalar10 (u a w : ℝ) : ℝ :=
  ((((((((-85066245 / 64 : ℝ) +
    (1591823865 / 256 : ℝ)*a^1) +
    ((-362372631 / 32 : ℝ)*a^1*w^2 +
    (27456465 / 8 : ℝ)*a^1*w^4)) +
    (((-1116369 / 4 : ℝ)*a^1*w^6 +
    (7029 / 1 : ℝ)*a^1*w^8) +
    ((-48 / 1 : ℝ)*a^1*w^10 +
    ((-2049802467 / 512 : ℝ)*a^2 +
    (71141415 / 128 : ℝ)*a^2*w^2)))) +
    ((((8575227 / 64 : ℝ)*a^2*w^4 +
    (-181809 / 16 : ℝ)*a^2*w^6) +
    ((156 / 1 : ℝ)*a^2*w^8 +
    (-327670217 / 2048 : ℝ)*a^3)) +
    (((-47506503 / 512 : ℝ)*a^3*w^2 +
    (3245571 / 256 : ℝ)*a^3*w^4) +
    ((-5313 / 16 : ℝ)*a^3*w^6 +
    ((3 / 4 : ℝ)*a^3*w^8 +
    (-1966854177 / 16384 : ℝ)*a^4))))) +
    (((((41303673 / 2048 : ℝ)*a^4*w^2 +
    (-678069 / 256 : ℝ)*a^4*w^4) +
    ((-183 / 64 : ℝ)*a^4*w^6 +
    (62366877 / 65536 : ℝ)*a^5)) +
    (((-5680107 / 4096 : ℝ)*a^5*w^2 +
    (34779 / 1024 : ℝ)*a^5*w^4) +
    ((-3218985 / 65536 : ℝ)*a^6 +
    ((37917 / 8192 : ℝ)*a^6*w^2 +
    (725859 / 262144 : ℝ)*a^7)))) +
    ((((-2761949 / 32 : ℝ)*u^1*a^1*w^1 +
    (-29327795 / 8 : ℝ)*u^1*a^1*w^3) +
    ((962001 / 1 : ℝ)*u^1*a^1*w^5 +
    (-50217 / 1 : ℝ)*u^1*a^1*w^7)) +
    (((584 / 1 : ℝ)*u^1*a^1*w^9 +
    (-6024239 / 12 : ℝ)*u^1*a^2*w^1) +
    ((-4705171 / 8 : ℝ)*u^1*a^2*w^3 +
    ((680721 / 8 : ℝ)*u^1*a^2*w^5 +
    (-2122 / 1 : ℝ)*u^1*a^2*w^7)))))) +
    ((((((4 / 1 : ℝ)*u^1*a^2*w^9 +
    (-564909 / 2 : ℝ)*u^1*a^3*w^1) +
    ((-8448057 / 128 : ℝ)*u^1*a^3*w^3 +
    (118857 / 32 : ℝ)*u^1*a^3*w^5)) +
    (((-97 / 4 : ℝ)*u^1*a^3*w^7 +
    (-61167255 / 1024 : ℝ)*u^1*a^4*w^1) +
    ((290829 / 128 : ℝ)*u^1*a^4*w^3 +
    ((3603 / 64 : ℝ)*u^1*a^4*w^5 +
    (834765 / 8192 : ℝ)*u^1*a^5*w^1)))) +
    ((((-455 / 512 : ℝ)*u^1*a^5*w^3 +
    (216879 / 16384 : ℝ)*u^1*a^6*w^1) +
    ((89303715 / 64 : ℝ)*u^2 +
    (-1184932685 / 384 : ℝ)*u^2*a^1)) +
    (((312055217 / 96 : ℝ)*u^2*a^1*w^2 +
    (-9374605 / 6 : ℝ)*u^2*a^1*w^4) +
    ((666059 / 4 : ℝ)*u^2*a^1*w^6 +
    ((-3618 / 1 : ℝ)*u^2*a^1*w^8 +
    (16 / 3 : ℝ)*u^2*a^1*w^10))))) +
    (((((4979588083 / 4608 : ℝ)*u^2*a^2 +
    (-30424517 / 96 : ℝ)*u^2*a^2*w^2) +
    ((-13030513 / 64 : ℝ)*u^2*a^2*w^4 +
    (90729 / 8 : ℝ)*u^2*a^2*w^6)) +
    (((-206 / 3 : ℝ)*u^2*a^2*w^8 +
    (-471677489 / 1536 : ℝ)*u^2*a^3) +
    ((-1603491 / 512 : ℝ)*u^2*a^3*w^2 +
    ((-2037343 / 128 : ℝ)*u^2*a^3*w^4 +
    (3757 / 16 : ℝ)*u^2*a^3*w^6)))) +
    ((((370732099 / 16384 : ℝ)*u^2*a^4 +
    (-8809353 / 1024 : ℝ)*u^2*a^4*w^2) +
    ((-11585 / 256 : ℝ)*u^2*a^4*w^4 +
    (2294295 / 32768 : ℝ)*u^2*a^5)) +
    (((-89533 / 4096 : ℝ)*u^2*a^5*w^2 +
    (370091 / 65536 : ℝ)*u^2*a^6) +
    ((136534609 / 288 : ℝ)*u^3*a^1*w^1 +
    ((11458235 / 18 : ℝ)*u^3*a^1*w^3 +
    (-758549 / 3 : ℝ)*u^3*a^1*w^5))))))) +
    (((((((36790 / 3 : ℝ)*u^3*a^1*w^7 +
    (-584 / 9 : ℝ)*u^3*a^1*w^9) +
    ((-15739319 / 72 : ℝ)*u^3*a^2*w^1 +
    (721789 / 8 : ℝ)*u^3*a^2*w^3)) +
    (((-1069817 / 36 : ℝ)*u^3*a^2*w^5 +
    (1324 / 3 : ℝ)*u^3*a^2*w^7) +
    ((-7011431 / 96 : ℝ)*u^3*a^3*w^1 +
    ((6460289 / 576 : ℝ)*u^3*a^3*w^3 +
    (-290569 / 288 : ℝ)*u^3*a^3*w^5)))) +
    ((((6109261 / 1536 : ℝ)*u^3*a^4*w^1 +
    (-108671 / 1152 : ℝ)*u^3*a^4*w^3) +
    ((5207539 / 73728 : ℝ)*u^3*a^5*w^1 +
    (-115580555 / 192 : ℝ)*u^4)) +
    (((5714767765 / 6912 : ℝ)*u^4*a^1 +
    (-31208975 / 144 : ℝ)*u^4*a^1*w^2) +
    ((6285595 / 36 : ℝ)*u^4*a^1*w^4 +
    ((-270569 / 12 : ℝ)*u^4*a^1*w^6 +
    (2837 / 9 : ℝ)*u^4*a^1*w^8))))) +
    (((((-2155468649 / 6912 : ℝ)*u^4*a^2 +
    (-11502847 / 576 : ℝ)*u^4*a^2*w^2) +
    ((38995115 / 1728 : ℝ)*u^4*a^2*w^4 +
    (-582715 / 432 : ℝ)*u^4*a^2*w^6)) +
    (((135031019 / 3072 : ℝ)*u^4*a^3 +
    (-68377453 / 4608 : ℝ)*u^4*a^3*w^2) +
    ((8891129 / 6912 : ℝ)*u^4*a^3*w^4 +
    ((-85945403 / 147456 : ℝ)*u^4*a^4 +
    (1959361 / 18432 : ℝ)*u^4*a^4*w^2)))) +
    ((((596311 / 1769472 : ℝ)*u^4*a^5 +
    (-76854289 / 1296 : ℝ)*u^5*a^1*w^1) +
    ((-2767 / 108 : ℝ)*u^5*a^1*w^3 +
    (18707 / 1 : ℝ)*u^5*a^1*w^5)) +
    (((-20051 / 27 : ℝ)*u^5*a^1*w^7 +
    (-2950709 / 108 : ℝ)*u^5*a^2*w^1) +
    ((-2111611 / 216 : ℝ)*u^5*a^2*w^3 +
    ((1012865 / 648 : ℝ)*u^5*a^2*w^5 +
    (5996833 / 864 : ℝ)*u^5*a^3*w^1)))))) +
    ((((((-1222945 / 1152 : ℝ)*u^5*a^3*w^3 +
    (2177555 / 27648 : ℝ)*u^5*a^4*w^1) +
    ((725531855 / 5184 : ℝ)*u^6 +
    (-2043498067 / 15552 : ℝ)*u^6*a^1)) +
    (((505927 / 1296 : ℝ)*u^6*a^1*w^2 +
    (-549383 / 162 : ℝ)*u^6*a^1*w^4) +
    ((269689 / 324 : ℝ)*u^6*a^1*w^6 +
    ((688241951 / 20736 : ℝ)*u^6*a^2 +
    (-43534273 / 7776 : ℝ)*u^6*a^2*w^2)))) +
    ((((-449939 / 576 : ℝ)*u^6*a^2*w^4 +
    (-197993117 / 124416 : ℝ)*u^6*a^3) +
    ((75002525 / 124416 : ℝ)*u^6*a^3*w^2 +
    (-3752845 / 3981312 : ℝ)*u^6*a^4)) +
    (((-14407493 / 3888 : ℝ)*u^7*a^1*w^1 +
    (-1751947 / 486 : ℝ)*u^7*a^1*w^3) +
    ((-67207 / 243 : ℝ)*u^7*a^1*w^5 +
    ((22067809 / 5832 : ℝ)*u^7*a^2*w^1 +
    (-593201 / 5832 : ℝ)*u^7*a^2*w^3))))) +
    (((((-704815 / 11664 : ℝ)*u^7*a^3*w^1 +
    (-296657725 / 15552 : ℝ)*u^8) +
    ((2139475247 / 186624 : ℝ)*u^8*a^1 +
    (-1222715 / 2592 : ℝ)*u^8*a^1*w^2)) +
    (((-102767 / 648 : ℝ)*u^8*a^1*w^4 +
    (-509040479 / 373248 : ℝ)*u^8*a^2) +
    ((93718277 / 279936 : ℝ)*u^8*a^2*w^2 +
    ((23049895 / 1492992 : ℝ)*u^8*a^3 +
    (141032879 / 209952 : ℝ)*u^9*a^1*w^1)))) +
    ((((503869 / 5832 : ℝ)*u^9*a^1*w^3 +
    (-681115 / 8748 : ℝ)*u^9*a^2*w^1) +
    ((7939225 / 5184 : ℝ)*u^10 +
    ((-1254566461 / 2519424 : ℝ)*u^10*a^1 +
    (8655751 / 209952 : ℝ)*u^10*a^1*w^2))) +
    (((200330885 / 10077696 : ℝ)*u^10*a^2 +
    (-34652003 / 1889568 : ℝ)*u^11*a^1*w^1) +
    ((-3139675 / 46656 : ℝ)*u^12 +
    ((389189099 / 45349632 : ℝ)*u^12*a^1 +
    (175175 / 139968 : ℝ)*u^14))))))))

/-- Symbolic normalization of the reflected jet before determinant formation. -/
theorem oddCompactReflectedScalar10_eq (u a w : ℝ) :
    MvPolynomial.eval (oddCompactState u a w) (oddCompactReflectedJetPolynomial 10) =
      (oddCompactReflectedScalar10 u a w : ℂ) := by
  have hf : MvPolynomial.eval (oddCompactState u a w)
      (oddCompactReflectedJetPolynomial 10) =
      ((((((1 : ℝ)*oddCompactSourceScalar0 u a w*oddCompactSourceScalar10 u a w +
    (-10 : ℝ)*oddCompactSourceScalar1 u a w*oddCompactSourceScalar9 u a w) +
    ((45 : ℝ)*oddCompactSourceScalar2 u a w*oddCompactSourceScalar8 u a w +
    ((-120 : ℝ)*oddCompactSourceScalar3 u a w*oddCompactSourceScalar7 u a w +
    (210 : ℝ)*oddCompactSourceScalar4 u a w*oddCompactSourceScalar6 u a w))) +
    (((-252 : ℝ)*oddCompactSourceScalar5 u a w*oddCompactSourceScalar5 u a w +
    ((210 : ℝ)*oddCompactSourceScalar6 u a w*oddCompactSourceScalar4 u a w +
    (-120 : ℝ)*oddCompactSourceScalar7 u a w*oddCompactSourceScalar3 u a w)) +
    ((45 : ℝ)*oddCompactSourceScalar8 u a w*oddCompactSourceScalar2 u a w +
    ((-10 : ℝ)*oddCompactSourceScalar9 u a w*oddCompactSourceScalar1 u a w +
    (1 : ℝ)*oddCompactSourceScalar10 u a w*oddCompactSourceScalar0 u a w)))) : ℝ) : ℂ) := by
    as_aux_lemma =>
      rw [eval_oddCompactReflectedJetPolynomial]
      norm_num only [Finset.sum_range_succ, Finset.sum_empty, Nat.choose, Nat.reduceSub, Nat.reduceAdd]
      simp only [oddCompactSourceScalar0_eq, oddCompactSourceScalar1_eq, oddCompactSourceScalar2_eq, oddCompactSourceScalar3_eq, oddCompactSourceScalar4_eq, oddCompactSourceScalar5_eq, oddCompactSourceScalar6_eq, oddCompactSourceScalar7_eq, oddCompactSourceScalar8_eq, oddCompactSourceScalar9_eq, oddCompactSourceScalar10_eq]
      push_cast
      ring
  rw [hf]
  apply congrArg Complex.ofReal
  as_aux_lemma =>
    unfold oddCompactSourceScalar0 oddCompactSourceScalar1 oddCompactSourceScalar2 oddCompactSourceScalar3 oddCompactSourceScalar4 oddCompactSourceScalar5 oddCompactSourceScalar6 oddCompactSourceScalar7 oddCompactSourceScalar8 oddCompactSourceScalar9 oddCompactSourceScalar10 oddCompactReflectedScalar10
    ring


end
end HTGeometry
