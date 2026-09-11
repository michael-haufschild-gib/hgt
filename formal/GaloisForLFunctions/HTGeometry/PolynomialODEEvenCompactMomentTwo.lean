import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactUnitCoordinates
import GaloisForLFunctions.HTGeometry.PolynomialODEEvenCompactGapPowers
import GaloisForLFunctions.HTGeometry.PolynomialODEOddCompactReflected4

/-! # Exact coupled-coordinate signed even moment 2 -/
namespace HTGeometry
noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000

/-- The signed even moment in fixed units, retaining the actual coupled source parameters. -/
def evenCompactUnitMomentTwo (r t v : ℝ) : ℝ :=
  (((((((107670089827/409600000000 : ℝ) +
    (422773827/102400000000 : ℝ)*t^1) +
    ((4729581/204800000000 : ℝ)*t^2 +
    (5927/102400000000 : ℝ)*t^3)) +
    (((27/409600000000 : ℝ)*t^4 +
    (-24859354931/460800000000 : ℝ)*r^1) +
    ((121968589/7680000000 : ℝ)*r^1*v^1 +
    ((69677373/40960000000 : ℝ)*r^1*v^2 +
    (20015701453/460800000000 : ℝ)*r^1*t^1)))) +
    ((((1171087/7680000000 : ℝ)*r^1*t^1*v^1 +
    (537849/40960000000 : ℝ)*r^1*t^1*v^2) +
    ((45234179/92160000000 : ℝ)*r^1*t^2 +
    (4507/7680000000 : ℝ)*r^1*t^2*v^1)) +
    (((1479/40960000000 : ℝ)*r^1*t^2*v^2 +
    (284269/153600000000 : ℝ)*r^1*t^3) +
    ((3/2560000000 : ℝ)*r^1*t^3*v^1 +
    ((3/40960000000 : ℝ)*r^1*t^3*v^2 +
    (9/3200000000 : ℝ)*r^1*t^4))))) +
    (((((95898851/76800000000 : ℝ)*r^2 +
    (-14321399/3840000000 : ℝ)*r^2*v^1) +
    ((-5554981/15360000000 : ℝ)*r^2*v^2 +
    (-28459/1024000000 : ℝ)*r^2*v^3)) +
    (((-573/102400000 : ℝ)*r^2*v^4 +
    (-147825989/23040000000 : ℝ)*r^2*t^1) +
    ((1028381/640000000 : ℝ)*r^2*t^1*v^1 +
    ((358599/2560000000 : ℝ)*r^2*t^1*v^2 +
    (21/512000000 : ℝ)*r^2*t^1*v^3)))) +
    ((((-3/102400000 : ℝ)*r^2*t^1*v^4 +
    (198774643/76800000000 : ℝ)*r^2*t^2) +
    ((47929/3840000000 : ℝ)*r^2*t^2*v^1 +
    (11911/15360000000 : ℝ)*r^2*t^2*v^2)) +
    (((1/1024000000 : ℝ)*r^2*t^2*v^3 +
    (6307/320000000 : ℝ)*r^2*t^3) +
    ((3/80000000 : ℝ)*r^2*t^3*v^1 +
    ((3/1280000000 : ℝ)*r^2*t^3*v^2 +
    (9/200000000 : ℝ)*r^2*t^4)))))) +
    ((((((17619601/97200000000 : ℝ)*r^3 +
    (636841/3240000000 : ℝ)*r^3*v^1) +
    ((206051/23040000000 : ℝ)*r^3*v^2 +
    (13967/2304000000 : ℝ)*r^3*v^3)) +
    (((407/307200000 : ℝ)*r^3*v^4 +
    (3254689/48600000000 : ℝ)*r^3*t^1) +
    ((-679201/3240000000 : ℝ)*r^3*t^1*v^1 +
    ((-1811/23040000000 : ℝ)*r^3*t^1*v^2 +
    (197/460800000 : ℝ)*r^3*t^1*v^3)))) +
    ((((-19/61440000 : ℝ)*r^3*t^1*v^4 +
    (-454099/2160000000 : ℝ)*r^3*t^2) +
    ((11873/180000000 : ℝ)*r^3*t^2*v^1 +
    (3037/720000000 : ℝ)*r^3*t^2*v^2)) +
    (((1/48000000 : ℝ)*r^3*t^2*v^3 +
    (94151/1350000000 : ℝ)*r^3*t^3) +
    ((1/2500000 : ℝ)*r^3*t^3*v^1 +
    ((1/40000000 : ℝ)*r^3*t^3*v^2 +
    (1/3125000 : ℝ)*r^3*t^4))))) +
    (((((-6031/6075000000 : ℝ)*r^4 +
    (1447/540000000 : ℝ)*r^4*v^1) +
    ((1163/960000000 : ℝ)*r^4*v^2 +
    (-31/96000000 : ℝ)*r^4*v^3)) +
    (((-1/12800000 : ℝ)*r^4*v^4 +
    (65051/9112500000 : ℝ)*r^4*t^1) +
    ((401/303750000 : ℝ)*r^4*t^1*v^1 +
    ((-4979/2160000000 : ℝ)*r^4*t^1*v^2 +
    (-23/216000000 : ℝ)*r^4*t^1*v^3)))) +
    ((((1/28800000 : ℝ)*r^4*t^1*v^4 +
    (-19541/6075000000 : ℝ)*r^4*t^2) +
    ((-437/101250000 : ℝ)*r^4*t^2*v^1 +
    (79/135000000 : ℝ)*r^4*t^2*v^2)) +
    (((1/9000000 : ℝ)*r^4*t^2*v^3 +
    (-227/126562500 : ℝ)*r^4*t^3) +
    ((1/703125 : ℝ)*r^4*t^3*v^1 +
    ((1/11250000 : ℝ)*r^4*t^3*v^2 +
    (1/1171875 : ℝ)*r^4*t^4)))))))

/-- Exact drift-square substitution; this identity assumes no sign or approximation. -/
theorem evenCompactUnitMomentTwo_eq (u t v : ℝ) :
    (-1 : ℝ)^2*(oddCompactReflectedScalar4 u (evenCompactUnitGap (u^2) t) (u*(1+v/4)))/(100 : ℝ)^2 = evenCompactUnitMomentTwo (u^2) t v := by
  unfold oddCompactReflectedScalar4
  rw [evenCompactUnitGap_pow_two, evenCompactUnitGap_pow_three, evenCompactUnitGap_pow_four]
  unfold evenCompactUnitGap evenCompactUnitGapPow2 evenCompactUnitGapPow3 evenCompactUnitGapPow4 evenCompactUnitMomentTwo
  ring

end
end HTGeometry
