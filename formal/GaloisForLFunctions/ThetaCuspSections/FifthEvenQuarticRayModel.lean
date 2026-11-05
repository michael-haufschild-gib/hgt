import GaloisForLFunctions.ThetaCuspSections.FifthEvenScaleEightData
import Mathlib.Algebra.Polynomial.Taylor

/-!
# A quartic cross-load reserve in fifth Gaussian coordinates

Set u=q/7-1 and z=exp(-3q)(q/7)^15. The pair weight lies between
zero and its rational enclosure at scale seven. Multiplication by
(1+u)^23 gives a degree-twenty-five matrix polynomial, affine in z.
Its endpoint coefficients are positive by exact Schur certificates.
Affine interpolation and nonnegative powers of u preserve positivity,
including the quartic load and the full-source error allowance 147/4000.
-/

noncomputable section
open Matrix Polynomial
namespace GaloisForLFunctions.ThetaCuspSections.QuarticRayCertificate
open FifthLeadingPair EightCrossData EvenFiveEndpoint

private def weightSeven : ℝ := 1/1300000000

private theorem cons5_two {α : Type*} (a : α) (f : Fin 4 → α) :
    Matrix.vecCons a f (2 : Fin 5) = f 1 := rfl
private theorem cons5_three {α : Type*} (a : α) (f : Fin 4 → α) :
    Matrix.vecCons a f (3 : Fin 5) = f 2 := rfl
private theorem cons5_four {α : Type*} (a : α) (f : Fin 4 → α) :
    Matrix.vecCons a f (4 : Fin 5) = f 3 := rfl
private theorem cons4_two {α : Type*} (a : α) (f : Fin 3 → α) :
    Matrix.vecCons a f (2 : Fin 4) = f 1 := rfl
private theorem cons4_three {α : Type*} (a : α) (f : Fin 3 → α) :
    Matrix.vecCons a f (3 : Fin 4) = f 2 := rfl
private theorem cons3_two {α : Type*} (a : α) (f : Fin 2 → α) :
    Matrix.vecCons a f (2 : Fin 3) = f 1 := rfl

private def rp0 (q : ℝ[X]) : ℝ[X] := 9 - q * 12 + q ^ 2 * 4
private def rp1 (q : ℝ[X]) : ℝ[X] := q * 120 - q ^ 2 * 96 + q ^ 3 * 32
private def rp2 (q : ℝ[X]) : ℝ[X] := -(q * 480) + q ^ 2 * 4416 - q ^ 3 * 2432 + q ^ 4 * 768
private def rp3 (q : ℝ[X]) : ℝ[X] := q * 1920 - q ^ 2 * 82176 + q ^ 3 * 253952 - q ^ 4 * 107520 + q ^ 5 * 30720
private def rp4 (q : ℝ[X]) : ℝ[X] := -(q * 7680) + q ^ 2 * 1360896 - q ^ 3 * 12388352 + q ^ 4 * 19611648 - q ^ 5 * 6881280 + q ^ 6 * 1720320
private def rp5 (q : ℝ[X]) : ℝ[X] := q * 30720 - q ^ 2 * 21958656 + q ^ 3 * 500252672 - q ^ 4 * 1924055040 + q ^ 5 * 1899233280 - q ^ 6 * 578027520 +
      q ^ 7 * 123863040
private def rp6 (q : ℝ[X]) : ℝ[X] := -(q * 122880) + q ^ 2 * 352075776 - q ^ 3 * 18886787072 + q ^ 4 * 150752329728 - q ^ 5 * 320229212160 +
          q ^ 6 * 221632266240 -
        q ^ 7 * 59949711360 +
      q ^ 8 * 10899947520
private def rp7 (q : ℝ[X]) : ℝ[X] := q * 491520 - q ^ 2 * 5636161536 + q ^ 3 * 694004744192 - q ^ 4 * 10699371970560 + q ^ 5 * 42564900618240 -
            q ^ 6 * 57797577277440 +
          q ^ 7 * 30323654000640 -
        q ^ 8 * 7368364523520 +
      q ^ 9 * 1133594542080
private def rp8 (q : ℝ[X]) : ℝ[X] := -(q * 1966080) + q ^ 2 * 90190381056 - q ^ 3 * 25209606766592 + q ^ 4 * 723521013547008 - q ^ 5 * 5015348591984640 +
              q ^ 6 * 11904065218805760 -
            q ^ 7 * 11342746988052480 +
          q ^ 8 * 4763364265820160 -
        q ^ 9 * 1042906978713600 +
      q ^ 10 * 136031345049600
private def bp0 (q : ℝ[X]) : ℝ[X] := 9 - q * 30 + q ^ 2 * 16
private def bp1 (q : ℝ[X]) : ℝ[X] := q * 300 - q ^ 2 * 1356 + q ^ 3 * 1400 - q ^ 4 * 576
private def bp2 (q : ℝ[X]) : ℝ[X] := -(q * 1200) + q ^ 2 * 39696 - q ^ 3 * 171200 + q ^ 4 * 200784 - q ^ 5 * 108000 + q ^ 6 * 20736
private def bp3 (q : ℝ[X]) : ℝ[X] := q * 4800 - q ^ 2 * 707136 + q ^ 3 * 10073600 - q ^ 4 * 35416896 + q ^ 5 * 43089600 - q ^ 6 * 25790400 +
        q ^ 7 * 7620480 -
      q ^ 8 * 746496
private def bp4 (q : ℝ[X]) : ℝ[X] := -(q * 19200) + q ^ 2 * 11602176 - q ^ 3 * 433126400 + q ^ 4 * 3651012864 - q ^ 5 * 10402022400 + q ^ 6 * 12499017216 -
            q ^ 7 * 7892398080 +
          q ^ 8 * 2788598016 -
        q ^ 9 * 468426240 +
      q ^ 10 * 26873856
private def bp5 (q : ℝ[X]) : ℝ[X] := q * 76800 - q ^ 2 * 186786816 + q ^ 3 * 16751820800 - q ^ 4 * 293872751616 + q ^ 5 * 1684623283200 -
                  q ^ 6 * 4002679526400 +
                q ^ 7 * 4618622453760 -
              q ^ 8 * 2987682527232 +
            q ^ 9 * 1157721984000 -
          q ^ 10 * 250538241024 +
        q ^ 11 * 26000455680 -
      q ^ 12 * 967458816
private def bp6 (q : ℝ[X]) : ℝ[X] := -(q * 307200) + q ^ 2 * 2993197056 - q ^ 3 * 621740441600 + q ^ 4 * 21146177900544 - q ^ 5 * 220856989900800 +
                      q ^ 6 * 939708531818496 -
                    q ^ 7 * 1911756612648960 +
                  q ^ 8 * 2090002567606272 -
                q ^ 9 * 1357634344366080 +
              q ^ 10 * 554264510164992 -
            q ^ 11 * 138376171929600 +
          q ^ 12 * 19385214160896 -
        q ^ 13 * 1342349107200 +
      q ^ 14 * 34828517376
private def bp7 (q : ℝ[X]) : ℝ[X] := q * 1228800 - q ^ 2 * 47909584896 + q ^ 3 * 22681960448000 - q ^ 4 * 1440287890292736 + q ^ 5 * 25873229882572800 -
                          q ^ 6 * 183368931293184000 +
                        q ^ 7 * 614258629468323840 -
                      q ^ 8 * 1091711196399403008 +
                    q ^ 9 * 1124791456149504000 -
                  q ^ 10 * 723717393839751168 +
                q ^ 11 * 304249765406146560 -
              q ^ 12 * 82936975037349888 +
            q ^ 13 * 13929931575705600 -
          q ^ 14 * 1338962033885184 +
        q ^ 15 * 65738826547200 -
      q ^ 16 * 1253826625536
private def bp8 (q : ℝ[X]) : ℝ[X] := -(q * 4915200) + q ^ 2 * 766627086336 - q ^ 3 * 821341473996800 + q ^ 4 * 95352120017485824 -
                                q ^ 5 * 2845887571309363200 +
                              q ^ 6 * 32060191465030680576 -
                            q ^ 7 * 167495442068487536640 +
                          q ^ 8 * 460233151236709613568 -
                        q ^ 9 * 725737675056009707520 +
                      q ^ 10 * 703779563626546987008 -
                    q ^ 11 * 444465339058343116800 +
                  q ^ 12 * 189568590591937609728 -
                q ^ 13 * 54676337965085491200 +
              q ^ 14 * 10342260481727397888 -
            q ^ 15 * 1222973202943180800 +
          q ^ 16 * 84812489945579520 -
        q ^ 17 * 3093817198510080 +
      q ^ 18 * 45137758519296

private def radial (q : ℝ[X]) : ℕ → ℝ[X]
  | 0 => rp0 q
  | 1 => rp1 q
  | 2 => rp2 q
  | 3 => rp3 q
  | 4 => rp4 q
  | 5 => rp5 q
  | 6 => rp6 q
  | 7 => rp7 q
  | 8 => rp8 q
  | _ => 0

private def mixed (q : ℝ[X]) : ℕ → ℝ[X]
  | 0 => bp0 q
  | 1 => bp1 q
  | 2 => bp2 q
  | 3 => bp3 q
  | 4 => bp4 q
  | 5 => bp5 q
  | 6 => bp6 q
  | 7 => bp7 q
  | 8 => bp8 q
  | _ => 0

private def factor : ℝ[X] := X+C 1
private def scale : ℝ[X] := 7*factor

private def moment (z : ℝ) (k : ℕ) : ℝ[X] :=
  C (((7:ℝ)^k)⁻¹)*(factor^(23-k)*radial scale k+
    C (8*z)*(factor^(8-k)*mixed scale k))


private theorem factor_coefficient (n k : ℕ) :
    (factor^n).coeff k = (n.choose k : ℝ) := by
  simp only [factor,Polynomial.coeff_X_add_C_pow,one_pow,one_mul]


private theorem factor_coeff (n : ℕ) : factor.coeff n = (Nat.choose 1 n : ℝ) := by
  simpa only [pow_one] using factor_coefficient 1 n

private def pick (n d : ℕ) : ℝ := (d.choose n : ℝ)

private def rCoefficient (k n : ℕ) : ℝ :=
  match k with
  | 0 => (9:ℝ)*7^0*pick n (23-0+0) - (12:ℝ)*7^1*pick n (23-0+1) + (4:ℝ)*7^2*pick n (23-0+2)
  | 1 => (120:ℝ)*7^1*pick n (23-1+1) - (96:ℝ)*7^2*pick n (23-1+2) + (32:ℝ)*7^3*pick n (23-1+3)
  | 2 => - (480:ℝ)*7^1*pick n (23-2+1) + (4416:ℝ)*7^2*pick n (23-2+2) - (2432:ℝ)*7^3*pick n (23-2+3) + (768:ℝ)*7^4*pick n (23-2+4)
  | 3 => (1920:ℝ)*7^1*pick n (23-3+1) - (82176:ℝ)*7^2*pick n (23-3+2) + (253952:ℝ)*7^3*pick n (23-3+3) - (107520:ℝ)*7^4*pick n (23-3+4) + (30720:ℝ)*7^5*pick n (23-3+5)
  | 4 => - (7680:ℝ)*7^1*pick n (23-4+1) + (1360896:ℝ)*7^2*pick n (23-4+2) - (12388352:ℝ)*7^3*pick n (23-4+3) + (19611648:ℝ)*7^4*pick n (23-4+4) - (6881280:ℝ)*7^5*pick n (23-4+5) + (1720320:ℝ)*7^6*pick n (23-4+6)
  | 5 => (30720:ℝ)*7^1*pick n (23-5+1) - (21958656:ℝ)*7^2*pick n (23-5+2) + (500252672:ℝ)*7^3*pick n (23-5+3) - (1924055040:ℝ)*7^4*pick n (23-5+4) + (1899233280:ℝ)*7^5*pick n (23-5+5) - (578027520:ℝ)*7^6*pick n (23-5+6) + (123863040:ℝ)*7^7*pick n (23-5+7)
  | 6 => - (122880:ℝ)*7^1*pick n (23-6+1) + (352075776:ℝ)*7^2*pick n (23-6+2) - (18886787072:ℝ)*7^3*pick n (23-6+3) + (150752329728:ℝ)*7^4*pick n (23-6+4) - (320229212160:ℝ)*7^5*pick n (23-6+5) + (221632266240:ℝ)*7^6*pick n (23-6+6) - (59949711360:ℝ)*7^7*pick n (23-6+7) + (10899947520:ℝ)*7^8*pick n (23-6+8)
  | 7 => (491520:ℝ)*7^1*pick n (23-7+1) - (5636161536:ℝ)*7^2*pick n (23-7+2) + (694004744192:ℝ)*7^3*pick n (23-7+3) - (10699371970560:ℝ)*7^4*pick n (23-7+4) + (42564900618240:ℝ)*7^5*pick n (23-7+5) - (57797577277440:ℝ)*7^6*pick n (23-7+6) + (30323654000640:ℝ)*7^7*pick n (23-7+7) - (7368364523520:ℝ)*7^8*pick n (23-7+8) + (1133594542080:ℝ)*7^9*pick n (23-7+9)
  | 8 => - (1966080:ℝ)*7^1*pick n (23-8+1) + (90190381056:ℝ)*7^2*pick n (23-8+2) - (25209606766592:ℝ)*7^3*pick n (23-8+3) + (723521013547008:ℝ)*7^4*pick n (23-8+4) - (5015348591984640:ℝ)*7^5*pick n (23-8+5) + (11904065218805760:ℝ)*7^6*pick n (23-8+6) - (11342746988052480:ℝ)*7^7*pick n (23-8+7) + (4763364265820160:ℝ)*7^8*pick n (23-8+8) - (1042906978713600:ℝ)*7^9*pick n (23-8+9) + (136031345049600:ℝ)*7^10*pick n (23-8+10)
  | _ => 0

private def bCoefficient (k n : ℕ) : ℝ :=
  match k with
  | 0 => (9:ℝ)*7^0*pick n (8-0+0) - (30:ℝ)*7^1*pick n (8-0+1) + (16:ℝ)*7^2*pick n (8-0+2)
  | 1 => (300:ℝ)*7^1*pick n (8-1+1) - (1356:ℝ)*7^2*pick n (8-1+2) + (1400:ℝ)*7^3*pick n (8-1+3) - (576:ℝ)*7^4*pick n (8-1+4)
  | 2 => - (1200:ℝ)*7^1*pick n (8-2+1) + (39696:ℝ)*7^2*pick n (8-2+2) - (171200:ℝ)*7^3*pick n (8-2+3) + (200784:ℝ)*7^4*pick n (8-2+4) - (108000:ℝ)*7^5*pick n (8-2+5) + (20736:ℝ)*7^6*pick n (8-2+6)
  | 3 => (4800:ℝ)*7^1*pick n (8-3+1) - (707136:ℝ)*7^2*pick n (8-3+2) + (10073600:ℝ)*7^3*pick n (8-3+3) - (35416896:ℝ)*7^4*pick n (8-3+4) + (43089600:ℝ)*7^5*pick n (8-3+5) - (25790400:ℝ)*7^6*pick n (8-3+6) + (7620480:ℝ)*7^7*pick n (8-3+7) - (746496:ℝ)*7^8*pick n (8-3+8)
  | 4 => - (19200:ℝ)*7^1*pick n (8-4+1) + (11602176:ℝ)*7^2*pick n (8-4+2) - (433126400:ℝ)*7^3*pick n (8-4+3) + (3651012864:ℝ)*7^4*pick n (8-4+4) - (10402022400:ℝ)*7^5*pick n (8-4+5) + (12499017216:ℝ)*7^6*pick n (8-4+6) - (7892398080:ℝ)*7^7*pick n (8-4+7) + (2788598016:ℝ)*7^8*pick n (8-4+8) - (468426240:ℝ)*7^9*pick n (8-4+9) + (26873856:ℝ)*7^10*pick n (8-4+10)
  | 5 => (76800:ℝ)*7^1*pick n (8-5+1) - (186786816:ℝ)*7^2*pick n (8-5+2) + (16751820800:ℝ)*7^3*pick n (8-5+3) - (293872751616:ℝ)*7^4*pick n (8-5+4) + (1684623283200:ℝ)*7^5*pick n (8-5+5) - (4002679526400:ℝ)*7^6*pick n (8-5+6) + (4618622453760:ℝ)*7^7*pick n (8-5+7) - (2987682527232:ℝ)*7^8*pick n (8-5+8) + (1157721984000:ℝ)*7^9*pick n (8-5+9) - (250538241024:ℝ)*7^10*pick n (8-5+10) + (26000455680:ℝ)*7^11*pick n (8-5+11) - (967458816:ℝ)*7^12*pick n (8-5+12)
  | 6 => - (307200:ℝ)*7^1*pick n (8-6+1) + (2993197056:ℝ)*7^2*pick n (8-6+2) - (621740441600:ℝ)*7^3*pick n (8-6+3) + (21146177900544:ℝ)*7^4*pick n (8-6+4) - (220856989900800:ℝ)*7^5*pick n (8-6+5) + (939708531818496:ℝ)*7^6*pick n (8-6+6) - (1911756612648960:ℝ)*7^7*pick n (8-6+7) + (2090002567606272:ℝ)*7^8*pick n (8-6+8) - (1357634344366080:ℝ)*7^9*pick n (8-6+9) + (554264510164992:ℝ)*7^10*pick n (8-6+10) - (138376171929600:ℝ)*7^11*pick n (8-6+11) + (19385214160896:ℝ)*7^12*pick n (8-6+12) - (1342349107200:ℝ)*7^13*pick n (8-6+13) + (34828517376:ℝ)*7^14*pick n (8-6+14)
  | 7 => (1228800:ℝ)*7^1*pick n (8-7+1) - (47909584896:ℝ)*7^2*pick n (8-7+2) + (22681960448000:ℝ)*7^3*pick n (8-7+3) - (1440287890292736:ℝ)*7^4*pick n (8-7+4) + (25873229882572800:ℝ)*7^5*pick n (8-7+5) - (183368931293184000:ℝ)*7^6*pick n (8-7+6) + (614258629468323840:ℝ)*7^7*pick n (8-7+7) - (1091711196399403008:ℝ)*7^8*pick n (8-7+8) + (1124791456149504000:ℝ)*7^9*pick n (8-7+9) - (723717393839751168:ℝ)*7^10*pick n (8-7+10) + (304249765406146560:ℝ)*7^11*pick n (8-7+11) - (82936975037349888:ℝ)*7^12*pick n (8-7+12) + (13929931575705600:ℝ)*7^13*pick n (8-7+13) - (1338962033885184:ℝ)*7^14*pick n (8-7+14) + (65738826547200:ℝ)*7^15*pick n (8-7+15) - (1253826625536:ℝ)*7^16*pick n (8-7+16)
  | 8 => - (4915200:ℝ)*7^1*pick n (8-8+1) + (766627086336:ℝ)*7^2*pick n (8-8+2) - (821341473996800:ℝ)*7^3*pick n (8-8+3) + (95352120017485824:ℝ)*7^4*pick n (8-8+4) - (2845887571309363200:ℝ)*7^5*pick n (8-8+5) + (32060191465030680576:ℝ)*7^6*pick n (8-8+6) - (167495442068487536640:ℝ)*7^7*pick n (8-8+7) + (460233151236709613568:ℝ)*7^8*pick n (8-8+8) - (725737675056009707520:ℝ)*7^9*pick n (8-8+9) + (703779563626546987008:ℝ)*7^10*pick n (8-8+10) - (444465339058343116800:ℝ)*7^11*pick n (8-8+11) + (189568590591937609728:ℝ)*7^12*pick n (8-8+12) - (54676337965085491200:ℝ)*7^13*pick n (8-8+13) + (10342260481727397888:ℝ)*7^14*pick n (8-8+14) - (1222973202943180800:ℝ)*7^15*pick n (8-8+15) + (84812489945579520:ℝ)*7^16*pick n (8-8+16) - (3093817198510080:ℝ)*7^17*pick n (8-8+17) + (45137758519296:ℝ)*7^18*pick n (8-8+18)
  | _ => 0

private def momentCoefficient (z : ℝ) (n k : ℕ) : ℝ :=
  ((7:ℝ)^k)⁻¹ * (rCoefficient k n+8*z*bCoefficient k n)

private theorem moment_coefficient_0 (z : ℝ) (n : ℕ) :
    (moment z 0).coeff n = momentCoefficient z n 0 := by
  norm_num [moment,momentCoefficient,scale,radial,mixed,rp0,bp0,rCoefficient,bCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick]
  ring

private theorem moment_coefficient_1 (z : ℝ) (n : ℕ) :
    (moment z 1).coeff n = momentCoefficient z n 1 := by
  norm_num [moment,momentCoefficient,scale,radial,mixed,rp1,bp1,rCoefficient,bCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick]
  ring

private theorem moment_coefficient_2 (z : ℝ) (n : ℕ) :
    (moment z 2).coeff n = momentCoefficient z n 2 := by
  norm_num [moment,momentCoefficient,scale,radial,mixed,rp2,bp2,rCoefficient,bCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick]
  ring

private theorem moment_coefficient_3 (z : ℝ) (n : ℕ) :
    (moment z 3).coeff n = momentCoefficient z n 3 := by
  norm_num [moment,momentCoefficient,scale,radial,mixed,rp3,bp3,rCoefficient,bCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick]
  ring

private theorem moment_coefficient_4 (z : ℝ) (n : ℕ) :
    (moment z 4).coeff n = momentCoefficient z n 4 := by
  norm_num [moment,momentCoefficient,scale,radial,mixed,rp4,bp4,rCoefficient,bCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick]
  ring

private theorem moment_coefficient_5 (z : ℝ) (n : ℕ) :
    (moment z 5).coeff n = momentCoefficient z n 5 := by
  norm_num [moment,momentCoefficient,scale,radial,mixed,rp5,bp5,rCoefficient,bCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick]
  ring

private theorem moment_coefficient_6 (z : ℝ) (n : ℕ) :
    (moment z 6).coeff n = momentCoefficient z n 6 := by
  norm_num [moment,momentCoefficient,scale,radial,mixed,rp6,bp6,rCoefficient,bCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick]
  ring

private theorem moment_coefficient_7 (z : ℝ) (n : ℕ) :
    (moment z 7).coeff n = momentCoefficient z n 7 := by
  norm_num [moment,momentCoefficient,scale,radial,mixed,rp7,bp7,rCoefficient,bCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick]
  ring

private theorem moment_coefficient_8 (z : ℝ) (n : ℕ) :
    (moment z 8).coeff n = momentCoefficient z n 8 := by
  norm_num [moment,momentCoefficient,scale,radial,mixed,rp8,bp8,rCoefficient,bCoefficient]
  ring_nf
  norm_num [Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
    Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick]
  ring

private theorem moment_coefficient (z : ℝ) (n k : ℕ) (hk : k ≤ 8) :
    (moment z k).coeff n = momentCoefficient z n k := by
  interval_cases k
  · exact moment_coefficient_0 z n
  · exact moment_coefficient_1 z n
  · exact moment_coefficient_2 z n
  · exact moment_coefficient_3 z n
  · exact moment_coefficient_4 z n
  · exact moment_coefficient_5 z n
  · exact moment_coefficient_6 z n
  · exact moment_coefficient_7 z n
  · exact moment_coefficient_8 z n

private def row0 : Fin 5 → ℝ[X] :=
  ![0,0,C (1/256)*factor^2,C (5/1024)*factor*(1-2*factor),
    C (35/2048)*factor*(factor-1)]
private def row1 : Fin 5 → ℝ[X] :=
  ![0,0,0,C (1/86016)*factor,C (1/24576)*(1-factor)]

private def rowZero : Fin 5 → Fin 3 → ℝ :=
  ![![0,0,0],![0,0,0],![0,0,1/256],![0,(8/7)*(35/8192),-80/8192],
    ![0,(8/7)*(-245/16384),280/16384]]

private def rowOne : Fin 5 → Fin 3 → ℝ :=
  ![![0,0,0],![0,0,0],![0,0,0],![0,(8/7)*(1/98304),0],
    ![(64/49)*(49/1572864),(8/7)*(-56/1572864),0]]


private def loadPolynomial (i j : Fin 5) : ℝ[X] :=
  factor^19*(C (paidSevenSchur 0 0)*row0 i*row0 j+
    C (paidSevenSchur 0 1)*(row0 i*row1 j+row1 i*row0 j)+
    C (paidSevenSchur 1 1)*row1 i*row1 j)

private def loadCoefficient (n : ℕ) (i j : Fin 5) : ℝ :=
  ∑ p : Fin 3, ∑ q : Fin 3,
    (paidSevenSchur 0 0*rowZero i p*rowZero j q+
      paidSevenSchur 0 1*(rowZero i p*rowOne j q+rowOne i p*rowZero j q)+
      paidSevenSchur 1 1*rowOne i p*rowOne j q)*pick n (19+p.val+q.val)

private theorem load_coefficient_row_0 (n : ℕ) (j : Fin 5) :
    (loadPolynomial 0 j).coeff n = loadCoefficient n 0 j := by
  unfold loadPolynomial loadCoefficient
  generalize paidSevenSchur 0 0 = a
  generalize paidSevenSchur 0 1 = b
  generalize paidSevenSchur 1 1 = c
  fin_cases j <;>
    norm_num [rowZero,rowOne,row0,row1,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Fin.ext_iff]

private theorem load_coefficient_row_1 (n : ℕ) (j : Fin 5) :
    (loadPolynomial 1 j).coeff n = loadCoefficient n 1 j := by
  unfold loadPolynomial loadCoefficient
  generalize paidSevenSchur 0 0 = a
  generalize paidSevenSchur 0 1 = b
  generalize paidSevenSchur 1 1 = c
  fin_cases j <;>
    norm_num [rowZero,rowOne,row0,row1,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Fin.ext_iff]

private theorem load_coefficient_row_2 (n : ℕ) (j : Fin 5) :
    (loadPolynomial 2 j).coeff n = loadCoefficient n 2 j := by
  unfold loadPolynomial loadCoefficient
  generalize paidSevenSchur 0 0 = a
  generalize paidSevenSchur 0 1 = b
  generalize paidSevenSchur 1 1 = c
  fin_cases j <;>
    norm_num [rowZero,rowOne,row0,row1,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Fin.ext_iff] <;>
    ring_nf <;>
    norm_num [← Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
      Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick] <;> ring

private theorem load_coefficient_row_3 (n : ℕ) (j : Fin 5) :
    (loadPolynomial 3 j).coeff n = loadCoefficient n 3 j := by
  unfold loadPolynomial loadCoefficient
  generalize paidSevenSchur 0 0 = a
  generalize paidSevenSchur 0 1 = b
  generalize paidSevenSchur 1 1 = c
  fin_cases j <;>
    norm_num [rowZero,rowOne,row0,row1,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Fin.ext_iff] <;>
    ring_nf <;>
    norm_num [← Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
      Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick] <;> ring

private theorem load_coefficient_row_4 (n : ℕ) (j : Fin 5) :
    (loadPolynomial 4 j).coeff n = loadCoefficient n 4 j := by
  unfold loadPolynomial loadCoefficient
  generalize paidSevenSchur 0 0 = a
  generalize paidSevenSchur 0 1 = b
  generalize paidSevenSchur 1 1 = c
  fin_cases j <;>
    norm_num [rowZero,rowOne,row0,row1,Fin.sum_univ_succ,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_succ,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Fin.ext_iff] <;>
    ring_nf <;>
    norm_num [← Polynomial.C_pow,Polynomial.coeff_add,Polynomial.coeff_sub,Polynomial.coeff_mul_C,
      Polynomial.coeff_C_mul,Polynomial.coeff_C,factor_coefficient,factor_coeff,pick] <;> ring

private theorem load_coefficient (n : ℕ) (i j : Fin 5) :
    (loadPolynomial i j).coeff n = loadCoefficient n i j := by
  fin_cases i
  · exact load_coefficient_row_0 n j
  · exact load_coefficient_row_1 n j
  · exact load_coefficient_row_2 n j
  · exact load_coefficient_row_3 n j
  · exact load_coefficient_row_4 n j

private def rayPolynomial (z : ℝ) (i j : Fin 5) : ℝ[X] :=
  (∑ u : Fin 5, ∑ v : Fin 5,
    C (gaussianBasis i u*gaussianBasis j v)*moment z (u.val+v.val))-
  C (3/20)*loadPolynomial i j-
  if i=j then C (147/4000)*factor^23 else 0

private def coefficient (z : ℝ) (n : ℕ) : Matrix (Fin 5) (Fin 5) ℝ :=
  fun i j => (rayPolynomial z i j).coeff n

private def fastCoefficient (z : ℝ) (n : ℕ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  (∑ u : Fin 5, ∑ v : Fin 5,
    gaussianBasis i u*gaussianBasis j v*momentCoefficient z n (u.val+v.val))-
  (3/20)*loadCoefficient n i j-
  if i=j then (147/4000)*pick n 23 else 0

private theorem coefficient_eq (z : ℝ) (n : ℕ) :
    coefficient z n = fastCoefficient z n := by
  ext i j
  have hm (u v : Fin 5) : (moment z (u.val+v.val)).coeff n =
      momentCoefficient z n (u.val+v.val) := moment_coefficient z n _ (by omega)
  simp only [coefficient,rayPolynomial,fastCoefficient,Polynomial.coeff_sub,
    Polynomial.finsetSum_coeff,Polynomial.coeff_C_mul,hm,load_coefficient]
  split_ifs <;> simp only [Polynomial.coeff_C_mul,factor_coefficient,pick,
    Polynomial.coeff_zero]

private theorem decay_seven : Real.exp (-21 : ℝ) ≤ weightSeven := by
  have he : (2718/1000 : ℝ) ≤ Real.exp 1 := by
    linarith only [Real.exp_one_gt_d9]
  have hp := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2718/1000) he 21
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat,mul_one] at hp
  have hlarge : (1300000000 : ℝ) ≤ Real.exp 21 := by
    exact le_trans (by norm_num) hp
  rw [Real.exp_neg,inv_eq_one_div]
  exact one_div_le_one_div_of_le (by norm_num) hlarge

/-- Exponential decay pays fifteen inverse powers from scale seven. -/
private theorem rescaled_weight_bounds {q : ℝ} (hq : 7 ≤ q) :
    0 ≤ Real.exp (-3*q)*(q/7)^15 ∧
      Real.exp (-3*q)*(q/7)^15 ≤ weightSeven := by
  have hq0 : 0 ≤ q/7 := by linarith only [hq]
  have hbase : q/7 ≤ Real.exp (q/7-1) := by
    linarith only [Real.add_one_le_exp (q/7-1)]
  have hp := pow_le_pow_left₀ hq0 hbase 15
  rw [← Real.exp_nat_mul] at hp
  norm_num only [Nat.cast_ofNat] at hp
  refine ⟨mul_nonneg (Real.exp_pos _).le (pow_nonneg hq0 _),?_⟩
  calc
    _ ≤ Real.exp (-3*q)*Real.exp (15*(q/7-1)) :=
      mul_le_mul_of_nonneg_left hp (Real.exp_pos _).le
    _ = Real.exp (-3*q+15*(q/7-1)) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-21 : ℝ) := Real.exp_le_exp.mpr (by linarith only [hq])
    _ ≤ weightSeven := decay_seven


private def e00 (m : ℕ → ℝ) : ℝ := m 0 * (999 / 1000)
private def e01 (m : ℕ → ℝ) : ℝ := -m 0 + m 1 * (1 / 8)
private def e02 (m : ℕ → ℝ) : ℝ := (m 0 * (3 / 4) + m 1 * (-3 / 16) + m 2 * (1 / 256) - 0)
private def e03 (m : ℕ → ℝ) : ℝ := (m 0 * (-5 / 8) + m 1 * (15 / 64) + m 2 * (-5 / 512) + m 3 * (1 / 12288) - 0)
private def e04 (m : ℕ → ℝ) : ℝ := (m 0 * (35 / 64) + m 1 * (-35 / 128) + m 2 * (35 / 2048) + m 3 * (-7 / 24576) + m 4 * (1 / 786432) -
      0)
private def e11 (m : ℕ → ℝ) : ℝ := m 0 * (999 / 1000) + m 1 * (-1 / 4) + m 2 * (1 / 64)
private def e12 (m : ℕ → ℝ) : ℝ := (m 0 * (-3 / 4) + m 1 * (9 / 32) + m 2 * (-7 / 256) + m 3 * (1 / 2048) - 0)
private def e13 (m : ℕ → ℝ) : ℝ := (m 0 * (5 / 8) + m 1 * (-5 / 16) + m 2 * (5 / 128) + m 3 * (-1 / 768) + m 4 * (1 / 98304) -
      0)
private def e14 (m : ℕ → ℝ) : ℝ := (m 0 * (-35 / 64) + m 1 * (175 / 512) + m 2 * (-105 / 2048) + m 3 * (119 / 49152) + m 4 * (-29 / 786432) +
        m 5 * (1 / 6291456) -
      0)
private def e22 (m : ℕ → ℝ) : ℝ := m 0 * (1123 / 2000) + m 1 * (-9 / 32) + m 2 * (21 / 512) + m 3 * (-3 / 2048) + m 4 * (1 / 65536)
private def e23 (m : ℕ → ℝ) : ℝ := (m 0 * (-15 / 32) + m 1 * (75 / 256) + m 2 * (-55 / 1024) + m 3 * (23 / 8192) + m 4 * (-7 / 131072) +
        m 5 * (1 / 3145728) -
      0)
private def e24 (m : ℕ → ℝ) : ℝ := (m 0 * (105 / 256) + m 1 * (-315 / 1024) + m 2 * (1085 / 16384) + m 3 * (-147 / 32768) + m 4 * (127 / 1048576) +
          m 5 * (-17 / 12582912) +
        m 6 * (1 / 201326592) -
      0)
private def e33 (m : ℕ → ℝ) : ℝ := m 0 * (3117 / 8000) + m 1 * (-75 / 256) + m 2 * (275 / 4096) + m 3 * (-115 / 24576) + m 4 * (35 / 262144) +
        m 5 * (-5 / 3145728) +
      m 6 * (1 / 150994944)
private def e34 (m : ℕ → ℝ) : ℝ := (m 0 * (-175 / 512) + m 1 * (1225 / 4096) + m 2 * (-2625 / 32768) + m 3 * (5425 / 786432) + m 4 * (-1615 / 6291456) +
            m 5 * (75 / 16777216) +
          m 6 * (-43 / 1207959552) +
        m 7 * (1 / 9663676416) -
      0)
private def e44 (m : ℕ → ℝ) : ℝ := m 0 * (152613 / 512000) + m 1 * (-1225 / 4096) + m 2 * (6125 / 65536) + m 3 * (-7595 / 786432) +
              m 4 * (11305 / 25165824) +
            m 5 * (-175 / 16777216) +
          m 6 * (301 / 2415919104) +
        m 7 * (-7 / 9663676416) +
      m 8 * (1 / 618475290624)
private def entryPoly (m : ℕ → ℝ) (i j : Fin 5) : ℝ :=
  match i.val,j.val with
  | 0,0 => e00 m
  | 0,1 | 1,0 => e01 m
  | 0,2 | 2,0 => e02 m
  | 0,3 | 3,0 => e03 m
  | 0,4 | 4,0 => e04 m
  | 1,1 => e11 m
  | 1,2 | 2,1 => e12 m
  | 1,3 | 3,1 => e13 m
  | 1,4 | 4,1 => e14 m
  | 2,2 => e22 m
  | 2,3 | 3,2 => e23 m
  | 2,4 | 4,2 => e24 m
  | 3,3 => e33 m
  | 3,4 | 4,3 => e34 m
  | 4,4 => e44 m
  | _,_ => 0

private def smallCoefficient (z : ℝ) (n : ℕ) : Matrix (Fin 5) (Fin 5) ℝ := fun i j =>
  entryPoly (momentCoefficient z n) i j - (3/20)*loadCoefficient n i j +
  if i=j then momentCoefficient z n 0/1000-(147/4000)*pick n 23 else 0


private theorem fast_small (z : ℝ) (n : ℕ) :
    fastCoefficient z n = smallCoefficient z n := by
  ext i j
  have h := FifthLeadingPair.entry_eq_entryPoly (momentCoefficient z n) i j
  change (∑ u : Fin 5, ∑ v : Fin 5,
      gaussianBasis i u*gaussianBasis j v*momentCoefficient z n (u.val+v.val))-
      (if i.val=j.val then momentCoefficient z n 0/1000 else 0)=
        entryPoly (momentCoefficient z n) i j at h
  simp only [← Fin.ext_iff] at h
  simp only [fastCoefficient,smallCoefficient]
  by_cases hij : i=j <;> simp only [hij,ite_true,ite_false] at h ⊢ <;>
    linarith only [h]

private theorem loadCoefficient_symmetric (n : ℕ) (i j : Fin 5) :
    loadCoefficient n i j = loadCoefficient n j i := by
  unfold loadCoefficient
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q _
  apply Finset.sum_congr rfl
  intro p _
  rw [show 19+p.val+q.val=19+q.val+p.val by omega]
  ring

private theorem entryPoly_symmetric (m : ℕ → ℝ) (i j : Fin 5) :
    entryPoly m i j = entryPoly m j i := by
  fin_cases i <;> fin_cases j <;> rfl

private theorem smallCoefficient_symmetric (z : ℝ) (n : ℕ) (i j : Fin 5) :
    smallCoefficient z n i j = smallCoefficient z n j i := by
  unfold smallCoefficient
  rw [entryPoly_symmetric _ i j,loadCoefficient_symmetric n i j]
  simp only [eq_comm]

private theorem coefficient_affine (w z : ℝ) (n : ℕ) :
    w • fastCoefficient z n = (w-z) • fastCoefficient 0 n+z • fastCoefficient w n := by
  ext i j
  have hm (k : ℕ) : w*momentCoefficient z n k =
      (w-z)*momentCoefficient 0 n k+z*momentCoefficient w n k := by
    unfold momentCoefficient
    ring
  have hsum : w*(∑ u : Fin 5, ∑ v : Fin 5,
      gaussianBasis i u*gaussianBasis j v*momentCoefficient z n (u.val+v.val)) =
      (w-z)*(∑ u : Fin 5, ∑ v : Fin 5,
        gaussianBasis i u*gaussianBasis j v*momentCoefficient 0 n (u.val+v.val))+
      z*(∑ u : Fin 5, ∑ v : Fin 5,
        gaussianBasis i u*gaussianBasis j v*momentCoefficient w n (u.val+v.val)) := by
    simp only [Finset.mul_sum,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    apply Finset.sum_congr rfl
    intro v _
    linear_combination gaussianBasis i u*gaussianBasis j v*hm (u.val+v.val)
  simp only [Matrix.smul_apply,Matrix.add_apply,smul_eq_mul,fastCoefficient]
  linear_combination hsum

private theorem mixed_coefficient_eq_zero (n k : ℕ)
    (hn : 19 ≤ n) (hk : k ≤ 8) : bCoefficient k n = 0 := by
  interval_cases k <;>
    simp (disch := omega) [bCoefficient,pick,Nat.choose_eq_zero_of_lt]

private theorem coefficient_weight_independent (z : ℝ) (n : ℕ) (hn : 19 ≤ n) :
    fastCoefficient z n = fastCoefficient 0 n := by
  ext i j
  have hm (u v : Fin 5) : momentCoefficient z n (u.val+v.val) =
      momentCoefficient 0 n (u.val+v.val) := by
    simp only [momentCoefficient,mixed_coefficient_eq_zero n (u.val+v.val) hn (by omega),
      mul_zero,add_zero]
  simp only [fastCoefficient,hm]

private theorem momentCoefficient_eq_zero (z : ℝ) (n k : ℕ)
    (hn : 25 < n) (hk : k ≤ 8) : momentCoefficient z n k = 0 := by
  interval_cases k <;>
    simp (disch := omega) [momentCoefficient,rCoefficient,bCoefficient,pick,
      Nat.choose_eq_zero_of_lt]

private theorem loadCoefficient_eq_zero (n : ℕ) (hn : 25 < n) (i j : Fin 5) :
    loadCoefficient n i j = 0 := by
  simp (disch := omega) [loadCoefficient,pick,Nat.choose_eq_zero_of_lt]

private theorem fastCoefficient_eq_zero (z : ℝ) (n : ℕ) (hn : 25 < n) :
    fastCoefficient z n = 0 := by
  ext i j
  have hm (u v : Fin 5) : momentCoefficient z n (u.val+v.val) = 0 :=
    momentCoefficient_eq_zero z n _ hn (by omega)
  have hp : pick n 23 = 0 := by
    simp only [pick,Nat.choose_eq_zero_of_lt (by omega : 23 < n),Nat.cast_zero]
  simp only [fastCoefficient,hm,loadCoefficient_eq_zero n hn,mul_zero,
    Finset.sum_const_zero,hp,ite_self,sub_zero,Matrix.zero_apply]


private theorem tailIndex_zero : tailIndex (0 : Fin 3) = (2 : Fin 5) := rfl
private theorem tailIndex_one : tailIndex (1 : Fin 3) = (3 : Fin 5) := rfl
private theorem tailIndex_two : tailIndex (2 : Fin 3) = (4 : Fin 5) := rfl


private def zero_0_moment_0 : {v : ℝ // momentCoefficient 0 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_0_moment_1 : {v : ℝ // momentCoefficient 0 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_0_moment_2 : {v : ℝ // momentCoefficient 0 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_0_moment_3 : {v : ℝ // momentCoefficient 0 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_0_moment_4 : {v : ℝ // momentCoefficient 0 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_0_moment_5 : {v : ℝ // momentCoefficient 0 0 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_0_moment_6 : {v : ℝ // momentCoefficient 0 0 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_0_moment_7 : {v : ℝ // momentCoefficient 0 0 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_0_moment_8 : {v : ℝ // momentCoefficient 0 0 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_0_cell_00 : {v : ℝ // smallCoefficient 0 0 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_0_moment_0.property]
      dsimp only [zero_0_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_01 : {v : ℝ // smallCoefficient 0 0 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_0_moment_0.property,zero_0_moment_1.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_02 : {v : ℝ // smallCoefficient 0 0 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_03 : {v : ℝ // smallCoefficient 0 0 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_04 : {v : ℝ // smallCoefficient 0 0 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property,zero_0_moment_4.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3,zero_0_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_11 : {v : ℝ // smallCoefficient 0 0 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_12 : {v : ℝ // smallCoefficient 0 0 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_13 : {v : ℝ // smallCoefficient 0 0 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property,zero_0_moment_4.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3,zero_0_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_14 : {v : ℝ // smallCoefficient 0 0 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property,zero_0_moment_4.property,zero_0_moment_5.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3,zero_0_moment_4,zero_0_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_22 : {v : ℝ // smallCoefficient 0 0 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property,zero_0_moment_4.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3,zero_0_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_23 : {v : ℝ // smallCoefficient 0 0 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property,zero_0_moment_4.property,zero_0_moment_5.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3,zero_0_moment_4,zero_0_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_24 : {v : ℝ // smallCoefficient 0 0 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property,zero_0_moment_4.property,zero_0_moment_5.property,zero_0_moment_6.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3,zero_0_moment_4,zero_0_moment_5,zero_0_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_33 : {v : ℝ // smallCoefficient 0 0 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property,zero_0_moment_4.property,zero_0_moment_5.property,zero_0_moment_6.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3,zero_0_moment_4,zero_0_moment_5,zero_0_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_34 : {v : ℝ // smallCoefficient 0 0 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property,zero_0_moment_4.property,zero_0_moment_5.property,zero_0_moment_6.property,zero_0_moment_7.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3,zero_0_moment_4,zero_0_moment_5,zero_0_moment_6,zero_0_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_cell_44 : {v : ℝ // smallCoefficient 0 0 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_0_moment_0.property,zero_0_moment_1.property,zero_0_moment_2.property,zero_0_moment_3.property,zero_0_moment_4.property,zero_0_moment_5.property,zero_0_moment_6.property,zero_0_moment_7.property,zero_0_moment_8.property]
      dsimp only [zero_0_moment_0,zero_0_moment_1,zero_0_moment_2,zero_0_moment_3,zero_0_moment_4,zero_0_moment_5,zero_0_moment_6,zero_0_moment_7,zero_0_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_0_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_0_cell_00.val,zero_0_cell_01.val,zero_0_cell_02.val,zero_0_cell_03.val,zero_0_cell_04.val],
    ![zero_0_cell_01.val,zero_0_cell_11.val,zero_0_cell_12.val,zero_0_cell_13.val,zero_0_cell_14.val],
    ![zero_0_cell_02.val,zero_0_cell_12.val,zero_0_cell_22.val,zero_0_cell_23.val,zero_0_cell_24.val],
    ![zero_0_cell_03.val,zero_0_cell_13.val,zero_0_cell_23.val,zero_0_cell_33.val,zero_0_cell_34.val],
    ![zero_0_cell_04.val,zero_0_cell_14.val,zero_0_cell_24.val,zero_0_cell_34.val,zero_0_cell_44.val]]

private theorem zero_0_matrix_eq : smallCoefficient 0 0=zero_0_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_0_cell_00.property
  · exact zero_0_cell_01.property
  · exact zero_0_cell_02.property
  · exact zero_0_cell_03.property
  · exact zero_0_cell_04.property
  · exact (smallCoefficient_symmetric 0 0 1 0).trans zero_0_cell_01.property
  · exact zero_0_cell_11.property
  · exact zero_0_cell_12.property
  · exact zero_0_cell_13.property
  · exact zero_0_cell_14.property
  · exact (smallCoefficient_symmetric 0 0 2 0).trans zero_0_cell_02.property
  · exact (smallCoefficient_symmetric 0 0 2 1).trans zero_0_cell_12.property
  · exact zero_0_cell_22.property
  · exact zero_0_cell_23.property
  · exact zero_0_cell_24.property
  · exact (smallCoefficient_symmetric 0 0 3 0).trans zero_0_cell_03.property
  · exact (smallCoefficient_symmetric 0 0 3 1).trans zero_0_cell_13.property
  · exact (smallCoefficient_symmetric 0 0 3 2).trans zero_0_cell_23.property
  · exact zero_0_cell_33.property
  · exact zero_0_cell_34.property
  · exact (smallCoefficient_symmetric 0 0 4 0).trans zero_0_cell_04.property
  · exact (smallCoefficient_symmetric 0 0 4 1).trans zero_0_cell_14.property
  · exact (smallCoefficient_symmetric 0 0 4 2).trans zero_0_cell_24.property
  · exact (smallCoefficient_symmetric 0 0 4 3).trans zero_0_cell_34.property
  · exact zero_0_cell_44.property

private theorem zero_0_first_pos : 0 < zero_0_matrix 0 0 := by
  dsimp only [zero_0_matrix,zero_0_cell_00,zero_0_cell_01,zero_0_cell_02,zero_0_cell_03,zero_0_cell_04,zero_0_cell_11,zero_0_cell_12,zero_0_cell_13,zero_0_cell_14,zero_0_cell_22,zero_0_cell_23,zero_0_cell_24,zero_0_cell_33,zero_0_cell_34,zero_0_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_0_delta_pos : 0 < delta zero_0_matrix := by
  dsimp only [zero_0_matrix,zero_0_cell_00,zero_0_cell_01,zero_0_cell_02,zero_0_cell_03,zero_0_cell_04,zero_0_cell_11,zero_0_cell_12,zero_0_cell_13,zero_0_cell_14,zero_0_cell_22,zero_0_cell_23,zero_0_cell_24,zero_0_cell_33,zero_0_cell_34,zero_0_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_0_schur_pos : 0 < schur zero_0_matrix 0 0 := by
  dsimp only [zero_0_matrix,zero_0_cell_00,zero_0_cell_01,zero_0_cell_02,zero_0_cell_03,zero_0_cell_04,zero_0_cell_11,zero_0_cell_12,zero_0_cell_13,zero_0_cell_14,zero_0_cell_22,zero_0_cell_23,zero_0_cell_24,zero_0_cell_33,zero_0_cell_34,zero_0_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_0_minor_pos : 0 < minor zero_0_matrix := by
  dsimp only [zero_0_matrix,zero_0_cell_00,zero_0_cell_01,zero_0_cell_02,zero_0_cell_03,zero_0_cell_04,zero_0_cell_11,zero_0_cell_12,zero_0_cell_13,zero_0_cell_14,zero_0_cell_22,zero_0_cell_23,zero_0_cell_24,zero_0_cell_33,zero_0_cell_34,zero_0_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_0_det_pos : 0 < determinant zero_0_matrix := by
  dsimp only [zero_0_matrix,zero_0_cell_00,zero_0_cell_01,zero_0_cell_02,zero_0_cell_03,zero_0_cell_04,zero_0_cell_11,zero_0_cell_12,zero_0_cell_13,zero_0_cell_14,zero_0_cell_22,zero_0_cell_23,zero_0_cell_24,zero_0_cell_33,zero_0_cell_34,zero_0_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_0_matrix_posDef : zero_0_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_0_first_pos zero_0_delta_pos zero_0_schur_pos
    zero_0_minor_pos zero_0_det_pos
  intro i j
  rw [← zero_0_matrix_eq]
  exact smallCoefficient_symmetric 0 0 i j

private theorem zero_0_posDef : (smallCoefficient 0 0).PosDef := by
  rw [zero_0_matrix_eq]
  exact zero_0_matrix_posDef


private def zero_1_moment_0 : {v : ℝ // momentCoefficient 0 1 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_1_moment_1 : {v : ℝ // momentCoefficient 0 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_1_moment_2 : {v : ℝ // momentCoefficient 0 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_1_moment_3 : {v : ℝ // momentCoefficient 0 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_1_moment_4 : {v : ℝ // momentCoefficient 0 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_1_moment_5 : {v : ℝ // momentCoefficient 0 1 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_1_moment_6 : {v : ℝ // momentCoefficient 0 1 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_1_moment_7 : {v : ℝ // momentCoefficient 0 1 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_1_moment_8 : {v : ℝ // momentCoefficient 0 1 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_1_cell_00 : {v : ℝ // smallCoefficient 0 1 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_1_moment_0.property]
      dsimp only [zero_1_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_01 : {v : ℝ // smallCoefficient 0 1 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_1_moment_0.property,zero_1_moment_1.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_02 : {v : ℝ // smallCoefficient 0 1 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_03 : {v : ℝ // smallCoefficient 0 1 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_04 : {v : ℝ // smallCoefficient 0 1 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property,zero_1_moment_4.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3,zero_1_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_11 : {v : ℝ // smallCoefficient 0 1 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_12 : {v : ℝ // smallCoefficient 0 1 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_13 : {v : ℝ // smallCoefficient 0 1 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property,zero_1_moment_4.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3,zero_1_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_14 : {v : ℝ // smallCoefficient 0 1 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property,zero_1_moment_4.property,zero_1_moment_5.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3,zero_1_moment_4,zero_1_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_22 : {v : ℝ // smallCoefficient 0 1 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property,zero_1_moment_4.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3,zero_1_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_23 : {v : ℝ // smallCoefficient 0 1 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property,zero_1_moment_4.property,zero_1_moment_5.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3,zero_1_moment_4,zero_1_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_24 : {v : ℝ // smallCoefficient 0 1 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property,zero_1_moment_4.property,zero_1_moment_5.property,zero_1_moment_6.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3,zero_1_moment_4,zero_1_moment_5,zero_1_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_33 : {v : ℝ // smallCoefficient 0 1 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property,zero_1_moment_4.property,zero_1_moment_5.property,zero_1_moment_6.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3,zero_1_moment_4,zero_1_moment_5,zero_1_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_34 : {v : ℝ // smallCoefficient 0 1 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property,zero_1_moment_4.property,zero_1_moment_5.property,zero_1_moment_6.property,zero_1_moment_7.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3,zero_1_moment_4,zero_1_moment_5,zero_1_moment_6,zero_1_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_cell_44 : {v : ℝ // smallCoefficient 0 1 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_1_moment_0.property,zero_1_moment_1.property,zero_1_moment_2.property,zero_1_moment_3.property,zero_1_moment_4.property,zero_1_moment_5.property,zero_1_moment_6.property,zero_1_moment_7.property,zero_1_moment_8.property]
      dsimp only [zero_1_moment_0,zero_1_moment_1,zero_1_moment_2,zero_1_moment_3,zero_1_moment_4,zero_1_moment_5,zero_1_moment_6,zero_1_moment_7,zero_1_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_1_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_1_cell_00.val,zero_1_cell_01.val,zero_1_cell_02.val,zero_1_cell_03.val,zero_1_cell_04.val],
    ![zero_1_cell_01.val,zero_1_cell_11.val,zero_1_cell_12.val,zero_1_cell_13.val,zero_1_cell_14.val],
    ![zero_1_cell_02.val,zero_1_cell_12.val,zero_1_cell_22.val,zero_1_cell_23.val,zero_1_cell_24.val],
    ![zero_1_cell_03.val,zero_1_cell_13.val,zero_1_cell_23.val,zero_1_cell_33.val,zero_1_cell_34.val],
    ![zero_1_cell_04.val,zero_1_cell_14.val,zero_1_cell_24.val,zero_1_cell_34.val,zero_1_cell_44.val]]

private theorem zero_1_matrix_eq : smallCoefficient 0 1=zero_1_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_1_cell_00.property
  · exact zero_1_cell_01.property
  · exact zero_1_cell_02.property
  · exact zero_1_cell_03.property
  · exact zero_1_cell_04.property
  · exact (smallCoefficient_symmetric 0 1 1 0).trans zero_1_cell_01.property
  · exact zero_1_cell_11.property
  · exact zero_1_cell_12.property
  · exact zero_1_cell_13.property
  · exact zero_1_cell_14.property
  · exact (smallCoefficient_symmetric 0 1 2 0).trans zero_1_cell_02.property
  · exact (smallCoefficient_symmetric 0 1 2 1).trans zero_1_cell_12.property
  · exact zero_1_cell_22.property
  · exact zero_1_cell_23.property
  · exact zero_1_cell_24.property
  · exact (smallCoefficient_symmetric 0 1 3 0).trans zero_1_cell_03.property
  · exact (smallCoefficient_symmetric 0 1 3 1).trans zero_1_cell_13.property
  · exact (smallCoefficient_symmetric 0 1 3 2).trans zero_1_cell_23.property
  · exact zero_1_cell_33.property
  · exact zero_1_cell_34.property
  · exact (smallCoefficient_symmetric 0 1 4 0).trans zero_1_cell_04.property
  · exact (smallCoefficient_symmetric 0 1 4 1).trans zero_1_cell_14.property
  · exact (smallCoefficient_symmetric 0 1 4 2).trans zero_1_cell_24.property
  · exact (smallCoefficient_symmetric 0 1 4 3).trans zero_1_cell_34.property
  · exact zero_1_cell_44.property

private theorem zero_1_first_pos : 0 < zero_1_matrix 0 0 := by
  dsimp only [zero_1_matrix,zero_1_cell_00,zero_1_cell_01,zero_1_cell_02,zero_1_cell_03,zero_1_cell_04,zero_1_cell_11,zero_1_cell_12,zero_1_cell_13,zero_1_cell_14,zero_1_cell_22,zero_1_cell_23,zero_1_cell_24,zero_1_cell_33,zero_1_cell_34,zero_1_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_1_delta_pos : 0 < delta zero_1_matrix := by
  dsimp only [zero_1_matrix,zero_1_cell_00,zero_1_cell_01,zero_1_cell_02,zero_1_cell_03,zero_1_cell_04,zero_1_cell_11,zero_1_cell_12,zero_1_cell_13,zero_1_cell_14,zero_1_cell_22,zero_1_cell_23,zero_1_cell_24,zero_1_cell_33,zero_1_cell_34,zero_1_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_1_schur_pos : 0 < schur zero_1_matrix 0 0 := by
  dsimp only [zero_1_matrix,zero_1_cell_00,zero_1_cell_01,zero_1_cell_02,zero_1_cell_03,zero_1_cell_04,zero_1_cell_11,zero_1_cell_12,zero_1_cell_13,zero_1_cell_14,zero_1_cell_22,zero_1_cell_23,zero_1_cell_24,zero_1_cell_33,zero_1_cell_34,zero_1_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_1_minor_pos : 0 < minor zero_1_matrix := by
  dsimp only [zero_1_matrix,zero_1_cell_00,zero_1_cell_01,zero_1_cell_02,zero_1_cell_03,zero_1_cell_04,zero_1_cell_11,zero_1_cell_12,zero_1_cell_13,zero_1_cell_14,zero_1_cell_22,zero_1_cell_23,zero_1_cell_24,zero_1_cell_33,zero_1_cell_34,zero_1_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_1_det_pos : 0 < determinant zero_1_matrix := by
  dsimp only [zero_1_matrix,zero_1_cell_00,zero_1_cell_01,zero_1_cell_02,zero_1_cell_03,zero_1_cell_04,zero_1_cell_11,zero_1_cell_12,zero_1_cell_13,zero_1_cell_14,zero_1_cell_22,zero_1_cell_23,zero_1_cell_24,zero_1_cell_33,zero_1_cell_34,zero_1_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_1_matrix_posDef : zero_1_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_1_first_pos zero_1_delta_pos zero_1_schur_pos
    zero_1_minor_pos zero_1_det_pos
  intro i j
  rw [← zero_1_matrix_eq]
  exact smallCoefficient_symmetric 0 1 i j

private theorem zero_1_posDef : (smallCoefficient 0 1).PosDef := by
  rw [zero_1_matrix_eq]
  exact zero_1_matrix_posDef


private def zero_2_moment_0 : {v : ℝ // momentCoefficient 0 2 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_2_moment_1 : {v : ℝ // momentCoefficient 0 2 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_2_moment_2 : {v : ℝ // momentCoefficient 0 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_2_moment_3 : {v : ℝ // momentCoefficient 0 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_2_moment_4 : {v : ℝ // momentCoefficient 0 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_2_moment_5 : {v : ℝ // momentCoefficient 0 2 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_2_moment_6 : {v : ℝ // momentCoefficient 0 2 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_2_moment_7 : {v : ℝ // momentCoefficient 0 2 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_2_moment_8 : {v : ℝ // momentCoefficient 0 2 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_2_cell_00 : {v : ℝ // smallCoefficient 0 2 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_2_moment_0.property]
      dsimp only [zero_2_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_01 : {v : ℝ // smallCoefficient 0 2 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_2_moment_0.property,zero_2_moment_1.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_02 : {v : ℝ // smallCoefficient 0 2 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_03 : {v : ℝ // smallCoefficient 0 2 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_04 : {v : ℝ // smallCoefficient 0 2 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property,zero_2_moment_4.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3,zero_2_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_11 : {v : ℝ // smallCoefficient 0 2 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_12 : {v : ℝ // smallCoefficient 0 2 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_13 : {v : ℝ // smallCoefficient 0 2 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property,zero_2_moment_4.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3,zero_2_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_14 : {v : ℝ // smallCoefficient 0 2 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property,zero_2_moment_4.property,zero_2_moment_5.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3,zero_2_moment_4,zero_2_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_22 : {v : ℝ // smallCoefficient 0 2 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property,zero_2_moment_4.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3,zero_2_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_23 : {v : ℝ // smallCoefficient 0 2 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property,zero_2_moment_4.property,zero_2_moment_5.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3,zero_2_moment_4,zero_2_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_24 : {v : ℝ // smallCoefficient 0 2 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property,zero_2_moment_4.property,zero_2_moment_5.property,zero_2_moment_6.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3,zero_2_moment_4,zero_2_moment_5,zero_2_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_33 : {v : ℝ // smallCoefficient 0 2 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property,zero_2_moment_4.property,zero_2_moment_5.property,zero_2_moment_6.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3,zero_2_moment_4,zero_2_moment_5,zero_2_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_34 : {v : ℝ // smallCoefficient 0 2 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property,zero_2_moment_4.property,zero_2_moment_5.property,zero_2_moment_6.property,zero_2_moment_7.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3,zero_2_moment_4,zero_2_moment_5,zero_2_moment_6,zero_2_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_cell_44 : {v : ℝ // smallCoefficient 0 2 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_2_moment_0.property,zero_2_moment_1.property,zero_2_moment_2.property,zero_2_moment_3.property,zero_2_moment_4.property,zero_2_moment_5.property,zero_2_moment_6.property,zero_2_moment_7.property,zero_2_moment_8.property]
      dsimp only [zero_2_moment_0,zero_2_moment_1,zero_2_moment_2,zero_2_moment_3,zero_2_moment_4,zero_2_moment_5,zero_2_moment_6,zero_2_moment_7,zero_2_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_2_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_2_cell_00.val,zero_2_cell_01.val,zero_2_cell_02.val,zero_2_cell_03.val,zero_2_cell_04.val],
    ![zero_2_cell_01.val,zero_2_cell_11.val,zero_2_cell_12.val,zero_2_cell_13.val,zero_2_cell_14.val],
    ![zero_2_cell_02.val,zero_2_cell_12.val,zero_2_cell_22.val,zero_2_cell_23.val,zero_2_cell_24.val],
    ![zero_2_cell_03.val,zero_2_cell_13.val,zero_2_cell_23.val,zero_2_cell_33.val,zero_2_cell_34.val],
    ![zero_2_cell_04.val,zero_2_cell_14.val,zero_2_cell_24.val,zero_2_cell_34.val,zero_2_cell_44.val]]

private theorem zero_2_matrix_eq : smallCoefficient 0 2=zero_2_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_2_cell_00.property
  · exact zero_2_cell_01.property
  · exact zero_2_cell_02.property
  · exact zero_2_cell_03.property
  · exact zero_2_cell_04.property
  · exact (smallCoefficient_symmetric 0 2 1 0).trans zero_2_cell_01.property
  · exact zero_2_cell_11.property
  · exact zero_2_cell_12.property
  · exact zero_2_cell_13.property
  · exact zero_2_cell_14.property
  · exact (smallCoefficient_symmetric 0 2 2 0).trans zero_2_cell_02.property
  · exact (smallCoefficient_symmetric 0 2 2 1).trans zero_2_cell_12.property
  · exact zero_2_cell_22.property
  · exact zero_2_cell_23.property
  · exact zero_2_cell_24.property
  · exact (smallCoefficient_symmetric 0 2 3 0).trans zero_2_cell_03.property
  · exact (smallCoefficient_symmetric 0 2 3 1).trans zero_2_cell_13.property
  · exact (smallCoefficient_symmetric 0 2 3 2).trans zero_2_cell_23.property
  · exact zero_2_cell_33.property
  · exact zero_2_cell_34.property
  · exact (smallCoefficient_symmetric 0 2 4 0).trans zero_2_cell_04.property
  · exact (smallCoefficient_symmetric 0 2 4 1).trans zero_2_cell_14.property
  · exact (smallCoefficient_symmetric 0 2 4 2).trans zero_2_cell_24.property
  · exact (smallCoefficient_symmetric 0 2 4 3).trans zero_2_cell_34.property
  · exact zero_2_cell_44.property

private theorem zero_2_first_pos : 0 < zero_2_matrix 0 0 := by
  dsimp only [zero_2_matrix,zero_2_cell_00,zero_2_cell_01,zero_2_cell_02,zero_2_cell_03,zero_2_cell_04,zero_2_cell_11,zero_2_cell_12,zero_2_cell_13,zero_2_cell_14,zero_2_cell_22,zero_2_cell_23,zero_2_cell_24,zero_2_cell_33,zero_2_cell_34,zero_2_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_2_delta_pos : 0 < delta zero_2_matrix := by
  dsimp only [zero_2_matrix,zero_2_cell_00,zero_2_cell_01,zero_2_cell_02,zero_2_cell_03,zero_2_cell_04,zero_2_cell_11,zero_2_cell_12,zero_2_cell_13,zero_2_cell_14,zero_2_cell_22,zero_2_cell_23,zero_2_cell_24,zero_2_cell_33,zero_2_cell_34,zero_2_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_2_schur_pos : 0 < schur zero_2_matrix 0 0 := by
  dsimp only [zero_2_matrix,zero_2_cell_00,zero_2_cell_01,zero_2_cell_02,zero_2_cell_03,zero_2_cell_04,zero_2_cell_11,zero_2_cell_12,zero_2_cell_13,zero_2_cell_14,zero_2_cell_22,zero_2_cell_23,zero_2_cell_24,zero_2_cell_33,zero_2_cell_34,zero_2_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_2_minor_pos : 0 < minor zero_2_matrix := by
  dsimp only [zero_2_matrix,zero_2_cell_00,zero_2_cell_01,zero_2_cell_02,zero_2_cell_03,zero_2_cell_04,zero_2_cell_11,zero_2_cell_12,zero_2_cell_13,zero_2_cell_14,zero_2_cell_22,zero_2_cell_23,zero_2_cell_24,zero_2_cell_33,zero_2_cell_34,zero_2_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_2_det_pos : 0 < determinant zero_2_matrix := by
  dsimp only [zero_2_matrix,zero_2_cell_00,zero_2_cell_01,zero_2_cell_02,zero_2_cell_03,zero_2_cell_04,zero_2_cell_11,zero_2_cell_12,zero_2_cell_13,zero_2_cell_14,zero_2_cell_22,zero_2_cell_23,zero_2_cell_24,zero_2_cell_33,zero_2_cell_34,zero_2_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_2_matrix_posDef : zero_2_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_2_first_pos zero_2_delta_pos zero_2_schur_pos
    zero_2_minor_pos zero_2_det_pos
  intro i j
  rw [← zero_2_matrix_eq]
  exact smallCoefficient_symmetric 0 2 i j

private theorem zero_2_posDef : (smallCoefficient 0 2).PosDef := by
  rw [zero_2_matrix_eq]
  exact zero_2_matrix_posDef


private def zero_3_moment_0 : {v : ℝ // momentCoefficient 0 3 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_3_moment_1 : {v : ℝ // momentCoefficient 0 3 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_3_moment_2 : {v : ℝ // momentCoefficient 0 3 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_3_moment_3 : {v : ℝ // momentCoefficient 0 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_3_moment_4 : {v : ℝ // momentCoefficient 0 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_3_moment_5 : {v : ℝ // momentCoefficient 0 3 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_3_moment_6 : {v : ℝ // momentCoefficient 0 3 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_3_moment_7 : {v : ℝ // momentCoefficient 0 3 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_3_moment_8 : {v : ℝ // momentCoefficient 0 3 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_3_cell_00 : {v : ℝ // smallCoefficient 0 3 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_3_moment_0.property]
      dsimp only [zero_3_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_01 : {v : ℝ // smallCoefficient 0 3 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_3_moment_0.property,zero_3_moment_1.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_02 : {v : ℝ // smallCoefficient 0 3 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_03 : {v : ℝ // smallCoefficient 0 3 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_04 : {v : ℝ // smallCoefficient 0 3 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property,zero_3_moment_4.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3,zero_3_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_11 : {v : ℝ // smallCoefficient 0 3 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_12 : {v : ℝ // smallCoefficient 0 3 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_13 : {v : ℝ // smallCoefficient 0 3 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property,zero_3_moment_4.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3,zero_3_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_14 : {v : ℝ // smallCoefficient 0 3 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property,zero_3_moment_4.property,zero_3_moment_5.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3,zero_3_moment_4,zero_3_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_22 : {v : ℝ // smallCoefficient 0 3 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property,zero_3_moment_4.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3,zero_3_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_23 : {v : ℝ // smallCoefficient 0 3 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property,zero_3_moment_4.property,zero_3_moment_5.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3,zero_3_moment_4,zero_3_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_24 : {v : ℝ // smallCoefficient 0 3 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property,zero_3_moment_4.property,zero_3_moment_5.property,zero_3_moment_6.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3,zero_3_moment_4,zero_3_moment_5,zero_3_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_33 : {v : ℝ // smallCoefficient 0 3 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property,zero_3_moment_4.property,zero_3_moment_5.property,zero_3_moment_6.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3,zero_3_moment_4,zero_3_moment_5,zero_3_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_34 : {v : ℝ // smallCoefficient 0 3 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property,zero_3_moment_4.property,zero_3_moment_5.property,zero_3_moment_6.property,zero_3_moment_7.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3,zero_3_moment_4,zero_3_moment_5,zero_3_moment_6,zero_3_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_cell_44 : {v : ℝ // smallCoefficient 0 3 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_3_moment_0.property,zero_3_moment_1.property,zero_3_moment_2.property,zero_3_moment_3.property,zero_3_moment_4.property,zero_3_moment_5.property,zero_3_moment_6.property,zero_3_moment_7.property,zero_3_moment_8.property]
      dsimp only [zero_3_moment_0,zero_3_moment_1,zero_3_moment_2,zero_3_moment_3,zero_3_moment_4,zero_3_moment_5,zero_3_moment_6,zero_3_moment_7,zero_3_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_3_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_3_cell_00.val,zero_3_cell_01.val,zero_3_cell_02.val,zero_3_cell_03.val,zero_3_cell_04.val],
    ![zero_3_cell_01.val,zero_3_cell_11.val,zero_3_cell_12.val,zero_3_cell_13.val,zero_3_cell_14.val],
    ![zero_3_cell_02.val,zero_3_cell_12.val,zero_3_cell_22.val,zero_3_cell_23.val,zero_3_cell_24.val],
    ![zero_3_cell_03.val,zero_3_cell_13.val,zero_3_cell_23.val,zero_3_cell_33.val,zero_3_cell_34.val],
    ![zero_3_cell_04.val,zero_3_cell_14.val,zero_3_cell_24.val,zero_3_cell_34.val,zero_3_cell_44.val]]

private theorem zero_3_matrix_eq : smallCoefficient 0 3=zero_3_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_3_cell_00.property
  · exact zero_3_cell_01.property
  · exact zero_3_cell_02.property
  · exact zero_3_cell_03.property
  · exact zero_3_cell_04.property
  · exact (smallCoefficient_symmetric 0 3 1 0).trans zero_3_cell_01.property
  · exact zero_3_cell_11.property
  · exact zero_3_cell_12.property
  · exact zero_3_cell_13.property
  · exact zero_3_cell_14.property
  · exact (smallCoefficient_symmetric 0 3 2 0).trans zero_3_cell_02.property
  · exact (smallCoefficient_symmetric 0 3 2 1).trans zero_3_cell_12.property
  · exact zero_3_cell_22.property
  · exact zero_3_cell_23.property
  · exact zero_3_cell_24.property
  · exact (smallCoefficient_symmetric 0 3 3 0).trans zero_3_cell_03.property
  · exact (smallCoefficient_symmetric 0 3 3 1).trans zero_3_cell_13.property
  · exact (smallCoefficient_symmetric 0 3 3 2).trans zero_3_cell_23.property
  · exact zero_3_cell_33.property
  · exact zero_3_cell_34.property
  · exact (smallCoefficient_symmetric 0 3 4 0).trans zero_3_cell_04.property
  · exact (smallCoefficient_symmetric 0 3 4 1).trans zero_3_cell_14.property
  · exact (smallCoefficient_symmetric 0 3 4 2).trans zero_3_cell_24.property
  · exact (smallCoefficient_symmetric 0 3 4 3).trans zero_3_cell_34.property
  · exact zero_3_cell_44.property

private theorem zero_3_first_pos : 0 < zero_3_matrix 0 0 := by
  dsimp only [zero_3_matrix,zero_3_cell_00,zero_3_cell_01,zero_3_cell_02,zero_3_cell_03,zero_3_cell_04,zero_3_cell_11,zero_3_cell_12,zero_3_cell_13,zero_3_cell_14,zero_3_cell_22,zero_3_cell_23,zero_3_cell_24,zero_3_cell_33,zero_3_cell_34,zero_3_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_3_delta_pos : 0 < delta zero_3_matrix := by
  dsimp only [zero_3_matrix,zero_3_cell_00,zero_3_cell_01,zero_3_cell_02,zero_3_cell_03,zero_3_cell_04,zero_3_cell_11,zero_3_cell_12,zero_3_cell_13,zero_3_cell_14,zero_3_cell_22,zero_3_cell_23,zero_3_cell_24,zero_3_cell_33,zero_3_cell_34,zero_3_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_3_schur_pos : 0 < schur zero_3_matrix 0 0 := by
  dsimp only [zero_3_matrix,zero_3_cell_00,zero_3_cell_01,zero_3_cell_02,zero_3_cell_03,zero_3_cell_04,zero_3_cell_11,zero_3_cell_12,zero_3_cell_13,zero_3_cell_14,zero_3_cell_22,zero_3_cell_23,zero_3_cell_24,zero_3_cell_33,zero_3_cell_34,zero_3_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_3_minor_pos : 0 < minor zero_3_matrix := by
  dsimp only [zero_3_matrix,zero_3_cell_00,zero_3_cell_01,zero_3_cell_02,zero_3_cell_03,zero_3_cell_04,zero_3_cell_11,zero_3_cell_12,zero_3_cell_13,zero_3_cell_14,zero_3_cell_22,zero_3_cell_23,zero_3_cell_24,zero_3_cell_33,zero_3_cell_34,zero_3_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_3_det_pos : 0 < determinant zero_3_matrix := by
  dsimp only [zero_3_matrix,zero_3_cell_00,zero_3_cell_01,zero_3_cell_02,zero_3_cell_03,zero_3_cell_04,zero_3_cell_11,zero_3_cell_12,zero_3_cell_13,zero_3_cell_14,zero_3_cell_22,zero_3_cell_23,zero_3_cell_24,zero_3_cell_33,zero_3_cell_34,zero_3_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_3_matrix_posDef : zero_3_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_3_first_pos zero_3_delta_pos zero_3_schur_pos
    zero_3_minor_pos zero_3_det_pos
  intro i j
  rw [← zero_3_matrix_eq]
  exact smallCoefficient_symmetric 0 3 i j

private theorem zero_3_posDef : (smallCoefficient 0 3).PosDef := by
  rw [zero_3_matrix_eq]
  exact zero_3_matrix_posDef


private def zero_4_moment_0 : {v : ℝ // momentCoefficient 0 4 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_4_moment_1 : {v : ℝ // momentCoefficient 0 4 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_4_moment_2 : {v : ℝ // momentCoefficient 0 4 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_4_moment_3 : {v : ℝ // momentCoefficient 0 4 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_4_moment_4 : {v : ℝ // momentCoefficient 0 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_4_moment_5 : {v : ℝ // momentCoefficient 0 4 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_4_moment_6 : {v : ℝ // momentCoefficient 0 4 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_4_moment_7 : {v : ℝ // momentCoefficient 0 4 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_4_moment_8 : {v : ℝ // momentCoefficient 0 4 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_4_cell_00 : {v : ℝ // smallCoefficient 0 4 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_4_moment_0.property]
      dsimp only [zero_4_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_01 : {v : ℝ // smallCoefficient 0 4 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_4_moment_0.property,zero_4_moment_1.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_02 : {v : ℝ // smallCoefficient 0 4 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_03 : {v : ℝ // smallCoefficient 0 4 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_04 : {v : ℝ // smallCoefficient 0 4 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property,zero_4_moment_4.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3,zero_4_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_11 : {v : ℝ // smallCoefficient 0 4 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_12 : {v : ℝ // smallCoefficient 0 4 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_13 : {v : ℝ // smallCoefficient 0 4 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property,zero_4_moment_4.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3,zero_4_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_14 : {v : ℝ // smallCoefficient 0 4 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property,zero_4_moment_4.property,zero_4_moment_5.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3,zero_4_moment_4,zero_4_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_22 : {v : ℝ // smallCoefficient 0 4 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property,zero_4_moment_4.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3,zero_4_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_23 : {v : ℝ // smallCoefficient 0 4 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property,zero_4_moment_4.property,zero_4_moment_5.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3,zero_4_moment_4,zero_4_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_24 : {v : ℝ // smallCoefficient 0 4 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property,zero_4_moment_4.property,zero_4_moment_5.property,zero_4_moment_6.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3,zero_4_moment_4,zero_4_moment_5,zero_4_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_33 : {v : ℝ // smallCoefficient 0 4 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property,zero_4_moment_4.property,zero_4_moment_5.property,zero_4_moment_6.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3,zero_4_moment_4,zero_4_moment_5,zero_4_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_34 : {v : ℝ // smallCoefficient 0 4 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property,zero_4_moment_4.property,zero_4_moment_5.property,zero_4_moment_6.property,zero_4_moment_7.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3,zero_4_moment_4,zero_4_moment_5,zero_4_moment_6,zero_4_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_cell_44 : {v : ℝ // smallCoefficient 0 4 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_4_moment_0.property,zero_4_moment_1.property,zero_4_moment_2.property,zero_4_moment_3.property,zero_4_moment_4.property,zero_4_moment_5.property,zero_4_moment_6.property,zero_4_moment_7.property,zero_4_moment_8.property]
      dsimp only [zero_4_moment_0,zero_4_moment_1,zero_4_moment_2,zero_4_moment_3,zero_4_moment_4,zero_4_moment_5,zero_4_moment_6,zero_4_moment_7,zero_4_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_4_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_4_cell_00.val,zero_4_cell_01.val,zero_4_cell_02.val,zero_4_cell_03.val,zero_4_cell_04.val],
    ![zero_4_cell_01.val,zero_4_cell_11.val,zero_4_cell_12.val,zero_4_cell_13.val,zero_4_cell_14.val],
    ![zero_4_cell_02.val,zero_4_cell_12.val,zero_4_cell_22.val,zero_4_cell_23.val,zero_4_cell_24.val],
    ![zero_4_cell_03.val,zero_4_cell_13.val,zero_4_cell_23.val,zero_4_cell_33.val,zero_4_cell_34.val],
    ![zero_4_cell_04.val,zero_4_cell_14.val,zero_4_cell_24.val,zero_4_cell_34.val,zero_4_cell_44.val]]

private theorem zero_4_matrix_eq : smallCoefficient 0 4=zero_4_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_4_cell_00.property
  · exact zero_4_cell_01.property
  · exact zero_4_cell_02.property
  · exact zero_4_cell_03.property
  · exact zero_4_cell_04.property
  · exact (smallCoefficient_symmetric 0 4 1 0).trans zero_4_cell_01.property
  · exact zero_4_cell_11.property
  · exact zero_4_cell_12.property
  · exact zero_4_cell_13.property
  · exact zero_4_cell_14.property
  · exact (smallCoefficient_symmetric 0 4 2 0).trans zero_4_cell_02.property
  · exact (smallCoefficient_symmetric 0 4 2 1).trans zero_4_cell_12.property
  · exact zero_4_cell_22.property
  · exact zero_4_cell_23.property
  · exact zero_4_cell_24.property
  · exact (smallCoefficient_symmetric 0 4 3 0).trans zero_4_cell_03.property
  · exact (smallCoefficient_symmetric 0 4 3 1).trans zero_4_cell_13.property
  · exact (smallCoefficient_symmetric 0 4 3 2).trans zero_4_cell_23.property
  · exact zero_4_cell_33.property
  · exact zero_4_cell_34.property
  · exact (smallCoefficient_symmetric 0 4 4 0).trans zero_4_cell_04.property
  · exact (smallCoefficient_symmetric 0 4 4 1).trans zero_4_cell_14.property
  · exact (smallCoefficient_symmetric 0 4 4 2).trans zero_4_cell_24.property
  · exact (smallCoefficient_symmetric 0 4 4 3).trans zero_4_cell_34.property
  · exact zero_4_cell_44.property

private theorem zero_4_first_pos : 0 < zero_4_matrix 0 0 := by
  dsimp only [zero_4_matrix,zero_4_cell_00,zero_4_cell_01,zero_4_cell_02,zero_4_cell_03,zero_4_cell_04,zero_4_cell_11,zero_4_cell_12,zero_4_cell_13,zero_4_cell_14,zero_4_cell_22,zero_4_cell_23,zero_4_cell_24,zero_4_cell_33,zero_4_cell_34,zero_4_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_4_delta_pos : 0 < delta zero_4_matrix := by
  dsimp only [zero_4_matrix,zero_4_cell_00,zero_4_cell_01,zero_4_cell_02,zero_4_cell_03,zero_4_cell_04,zero_4_cell_11,zero_4_cell_12,zero_4_cell_13,zero_4_cell_14,zero_4_cell_22,zero_4_cell_23,zero_4_cell_24,zero_4_cell_33,zero_4_cell_34,zero_4_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_4_schur_pos : 0 < schur zero_4_matrix 0 0 := by
  dsimp only [zero_4_matrix,zero_4_cell_00,zero_4_cell_01,zero_4_cell_02,zero_4_cell_03,zero_4_cell_04,zero_4_cell_11,zero_4_cell_12,zero_4_cell_13,zero_4_cell_14,zero_4_cell_22,zero_4_cell_23,zero_4_cell_24,zero_4_cell_33,zero_4_cell_34,zero_4_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_4_minor_pos : 0 < minor zero_4_matrix := by
  dsimp only [zero_4_matrix,zero_4_cell_00,zero_4_cell_01,zero_4_cell_02,zero_4_cell_03,zero_4_cell_04,zero_4_cell_11,zero_4_cell_12,zero_4_cell_13,zero_4_cell_14,zero_4_cell_22,zero_4_cell_23,zero_4_cell_24,zero_4_cell_33,zero_4_cell_34,zero_4_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_4_det_pos : 0 < determinant zero_4_matrix := by
  dsimp only [zero_4_matrix,zero_4_cell_00,zero_4_cell_01,zero_4_cell_02,zero_4_cell_03,zero_4_cell_04,zero_4_cell_11,zero_4_cell_12,zero_4_cell_13,zero_4_cell_14,zero_4_cell_22,zero_4_cell_23,zero_4_cell_24,zero_4_cell_33,zero_4_cell_34,zero_4_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_4_matrix_posDef : zero_4_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_4_first_pos zero_4_delta_pos zero_4_schur_pos
    zero_4_minor_pos zero_4_det_pos
  intro i j
  rw [← zero_4_matrix_eq]
  exact smallCoefficient_symmetric 0 4 i j

private theorem zero_4_posDef : (smallCoefficient 0 4).PosDef := by
  rw [zero_4_matrix_eq]
  exact zero_4_matrix_posDef


private def zero_5_moment_0 : {v : ℝ // momentCoefficient 0 5 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_5_moment_1 : {v : ℝ // momentCoefficient 0 5 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_5_moment_2 : {v : ℝ // momentCoefficient 0 5 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_5_moment_3 : {v : ℝ // momentCoefficient 0 5 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_5_moment_4 : {v : ℝ // momentCoefficient 0 5 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_5_moment_5 : {v : ℝ // momentCoefficient 0 5 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_5_moment_6 : {v : ℝ // momentCoefficient 0 5 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_5_moment_7 : {v : ℝ // momentCoefficient 0 5 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_5_moment_8 : {v : ℝ // momentCoefficient 0 5 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_5_cell_00 : {v : ℝ // smallCoefficient 0 5 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_5_moment_0.property]
      dsimp only [zero_5_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_01 : {v : ℝ // smallCoefficient 0 5 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_5_moment_0.property,zero_5_moment_1.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_02 : {v : ℝ // smallCoefficient 0 5 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_03 : {v : ℝ // smallCoefficient 0 5 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_04 : {v : ℝ // smallCoefficient 0 5 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property,zero_5_moment_4.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3,zero_5_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_11 : {v : ℝ // smallCoefficient 0 5 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_12 : {v : ℝ // smallCoefficient 0 5 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_13 : {v : ℝ // smallCoefficient 0 5 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property,zero_5_moment_4.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3,zero_5_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_14 : {v : ℝ // smallCoefficient 0 5 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property,zero_5_moment_4.property,zero_5_moment_5.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3,zero_5_moment_4,zero_5_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_22 : {v : ℝ // smallCoefficient 0 5 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property,zero_5_moment_4.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3,zero_5_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_23 : {v : ℝ // smallCoefficient 0 5 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property,zero_5_moment_4.property,zero_5_moment_5.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3,zero_5_moment_4,zero_5_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_24 : {v : ℝ // smallCoefficient 0 5 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property,zero_5_moment_4.property,zero_5_moment_5.property,zero_5_moment_6.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3,zero_5_moment_4,zero_5_moment_5,zero_5_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_33 : {v : ℝ // smallCoefficient 0 5 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property,zero_5_moment_4.property,zero_5_moment_5.property,zero_5_moment_6.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3,zero_5_moment_4,zero_5_moment_5,zero_5_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_34 : {v : ℝ // smallCoefficient 0 5 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property,zero_5_moment_4.property,zero_5_moment_5.property,zero_5_moment_6.property,zero_5_moment_7.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3,zero_5_moment_4,zero_5_moment_5,zero_5_moment_6,zero_5_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_cell_44 : {v : ℝ // smallCoefficient 0 5 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_5_moment_0.property,zero_5_moment_1.property,zero_5_moment_2.property,zero_5_moment_3.property,zero_5_moment_4.property,zero_5_moment_5.property,zero_5_moment_6.property,zero_5_moment_7.property,zero_5_moment_8.property]
      dsimp only [zero_5_moment_0,zero_5_moment_1,zero_5_moment_2,zero_5_moment_3,zero_5_moment_4,zero_5_moment_5,zero_5_moment_6,zero_5_moment_7,zero_5_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_5_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_5_cell_00.val,zero_5_cell_01.val,zero_5_cell_02.val,zero_5_cell_03.val,zero_5_cell_04.val],
    ![zero_5_cell_01.val,zero_5_cell_11.val,zero_5_cell_12.val,zero_5_cell_13.val,zero_5_cell_14.val],
    ![zero_5_cell_02.val,zero_5_cell_12.val,zero_5_cell_22.val,zero_5_cell_23.val,zero_5_cell_24.val],
    ![zero_5_cell_03.val,zero_5_cell_13.val,zero_5_cell_23.val,zero_5_cell_33.val,zero_5_cell_34.val],
    ![zero_5_cell_04.val,zero_5_cell_14.val,zero_5_cell_24.val,zero_5_cell_34.val,zero_5_cell_44.val]]

private theorem zero_5_matrix_eq : smallCoefficient 0 5=zero_5_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_5_cell_00.property
  · exact zero_5_cell_01.property
  · exact zero_5_cell_02.property
  · exact zero_5_cell_03.property
  · exact zero_5_cell_04.property
  · exact (smallCoefficient_symmetric 0 5 1 0).trans zero_5_cell_01.property
  · exact zero_5_cell_11.property
  · exact zero_5_cell_12.property
  · exact zero_5_cell_13.property
  · exact zero_5_cell_14.property
  · exact (smallCoefficient_symmetric 0 5 2 0).trans zero_5_cell_02.property
  · exact (smallCoefficient_symmetric 0 5 2 1).trans zero_5_cell_12.property
  · exact zero_5_cell_22.property
  · exact zero_5_cell_23.property
  · exact zero_5_cell_24.property
  · exact (smallCoefficient_symmetric 0 5 3 0).trans zero_5_cell_03.property
  · exact (smallCoefficient_symmetric 0 5 3 1).trans zero_5_cell_13.property
  · exact (smallCoefficient_symmetric 0 5 3 2).trans zero_5_cell_23.property
  · exact zero_5_cell_33.property
  · exact zero_5_cell_34.property
  · exact (smallCoefficient_symmetric 0 5 4 0).trans zero_5_cell_04.property
  · exact (smallCoefficient_symmetric 0 5 4 1).trans zero_5_cell_14.property
  · exact (smallCoefficient_symmetric 0 5 4 2).trans zero_5_cell_24.property
  · exact (smallCoefficient_symmetric 0 5 4 3).trans zero_5_cell_34.property
  · exact zero_5_cell_44.property

private theorem zero_5_first_pos : 0 < zero_5_matrix 0 0 := by
  dsimp only [zero_5_matrix,zero_5_cell_00,zero_5_cell_01,zero_5_cell_02,zero_5_cell_03,zero_5_cell_04,zero_5_cell_11,zero_5_cell_12,zero_5_cell_13,zero_5_cell_14,zero_5_cell_22,zero_5_cell_23,zero_5_cell_24,zero_5_cell_33,zero_5_cell_34,zero_5_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_5_delta_pos : 0 < delta zero_5_matrix := by
  dsimp only [zero_5_matrix,zero_5_cell_00,zero_5_cell_01,zero_5_cell_02,zero_5_cell_03,zero_5_cell_04,zero_5_cell_11,zero_5_cell_12,zero_5_cell_13,zero_5_cell_14,zero_5_cell_22,zero_5_cell_23,zero_5_cell_24,zero_5_cell_33,zero_5_cell_34,zero_5_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_5_schur_pos : 0 < schur zero_5_matrix 0 0 := by
  dsimp only [zero_5_matrix,zero_5_cell_00,zero_5_cell_01,zero_5_cell_02,zero_5_cell_03,zero_5_cell_04,zero_5_cell_11,zero_5_cell_12,zero_5_cell_13,zero_5_cell_14,zero_5_cell_22,zero_5_cell_23,zero_5_cell_24,zero_5_cell_33,zero_5_cell_34,zero_5_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_5_minor_pos : 0 < minor zero_5_matrix := by
  dsimp only [zero_5_matrix,zero_5_cell_00,zero_5_cell_01,zero_5_cell_02,zero_5_cell_03,zero_5_cell_04,zero_5_cell_11,zero_5_cell_12,zero_5_cell_13,zero_5_cell_14,zero_5_cell_22,zero_5_cell_23,zero_5_cell_24,zero_5_cell_33,zero_5_cell_34,zero_5_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_5_det_pos : 0 < determinant zero_5_matrix := by
  dsimp only [zero_5_matrix,zero_5_cell_00,zero_5_cell_01,zero_5_cell_02,zero_5_cell_03,zero_5_cell_04,zero_5_cell_11,zero_5_cell_12,zero_5_cell_13,zero_5_cell_14,zero_5_cell_22,zero_5_cell_23,zero_5_cell_24,zero_5_cell_33,zero_5_cell_34,zero_5_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_5_matrix_posDef : zero_5_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_5_first_pos zero_5_delta_pos zero_5_schur_pos
    zero_5_minor_pos zero_5_det_pos
  intro i j
  rw [← zero_5_matrix_eq]
  exact smallCoefficient_symmetric 0 5 i j

private theorem zero_5_posDef : (smallCoefficient 0 5).PosDef := by
  rw [zero_5_matrix_eq]
  exact zero_5_matrix_posDef


private def zero_6_moment_0 : {v : ℝ // momentCoefficient 0 6 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_6_moment_1 : {v : ℝ // momentCoefficient 0 6 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_6_moment_2 : {v : ℝ // momentCoefficient 0 6 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_6_moment_3 : {v : ℝ // momentCoefficient 0 6 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_6_moment_4 : {v : ℝ // momentCoefficient 0 6 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_6_moment_5 : {v : ℝ // momentCoefficient 0 6 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_6_moment_6 : {v : ℝ // momentCoefficient 0 6 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_6_moment_7 : {v : ℝ // momentCoefficient 0 6 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_6_moment_8 : {v : ℝ // momentCoefficient 0 6 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_6_cell_00 : {v : ℝ // smallCoefficient 0 6 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_6_moment_0.property]
      dsimp only [zero_6_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_01 : {v : ℝ // smallCoefficient 0 6 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_6_moment_0.property,zero_6_moment_1.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_02 : {v : ℝ // smallCoefficient 0 6 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_03 : {v : ℝ // smallCoefficient 0 6 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_04 : {v : ℝ // smallCoefficient 0 6 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property,zero_6_moment_4.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3,zero_6_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_11 : {v : ℝ // smallCoefficient 0 6 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_12 : {v : ℝ // smallCoefficient 0 6 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_13 : {v : ℝ // smallCoefficient 0 6 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property,zero_6_moment_4.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3,zero_6_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_14 : {v : ℝ // smallCoefficient 0 6 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property,zero_6_moment_4.property,zero_6_moment_5.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3,zero_6_moment_4,zero_6_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_22 : {v : ℝ // smallCoefficient 0 6 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property,zero_6_moment_4.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3,zero_6_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_23 : {v : ℝ // smallCoefficient 0 6 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property,zero_6_moment_4.property,zero_6_moment_5.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3,zero_6_moment_4,zero_6_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_24 : {v : ℝ // smallCoefficient 0 6 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property,zero_6_moment_4.property,zero_6_moment_5.property,zero_6_moment_6.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3,zero_6_moment_4,zero_6_moment_5,zero_6_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_33 : {v : ℝ // smallCoefficient 0 6 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property,zero_6_moment_4.property,zero_6_moment_5.property,zero_6_moment_6.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3,zero_6_moment_4,zero_6_moment_5,zero_6_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_34 : {v : ℝ // smallCoefficient 0 6 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property,zero_6_moment_4.property,zero_6_moment_5.property,zero_6_moment_6.property,zero_6_moment_7.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3,zero_6_moment_4,zero_6_moment_5,zero_6_moment_6,zero_6_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_cell_44 : {v : ℝ // smallCoefficient 0 6 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_6_moment_0.property,zero_6_moment_1.property,zero_6_moment_2.property,zero_6_moment_3.property,zero_6_moment_4.property,zero_6_moment_5.property,zero_6_moment_6.property,zero_6_moment_7.property,zero_6_moment_8.property]
      dsimp only [zero_6_moment_0,zero_6_moment_1,zero_6_moment_2,zero_6_moment_3,zero_6_moment_4,zero_6_moment_5,zero_6_moment_6,zero_6_moment_7,zero_6_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_6_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_6_cell_00.val,zero_6_cell_01.val,zero_6_cell_02.val,zero_6_cell_03.val,zero_6_cell_04.val],
    ![zero_6_cell_01.val,zero_6_cell_11.val,zero_6_cell_12.val,zero_6_cell_13.val,zero_6_cell_14.val],
    ![zero_6_cell_02.val,zero_6_cell_12.val,zero_6_cell_22.val,zero_6_cell_23.val,zero_6_cell_24.val],
    ![zero_6_cell_03.val,zero_6_cell_13.val,zero_6_cell_23.val,zero_6_cell_33.val,zero_6_cell_34.val],
    ![zero_6_cell_04.val,zero_6_cell_14.val,zero_6_cell_24.val,zero_6_cell_34.val,zero_6_cell_44.val]]

private theorem zero_6_matrix_eq : smallCoefficient 0 6=zero_6_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_6_cell_00.property
  · exact zero_6_cell_01.property
  · exact zero_6_cell_02.property
  · exact zero_6_cell_03.property
  · exact zero_6_cell_04.property
  · exact (smallCoefficient_symmetric 0 6 1 0).trans zero_6_cell_01.property
  · exact zero_6_cell_11.property
  · exact zero_6_cell_12.property
  · exact zero_6_cell_13.property
  · exact zero_6_cell_14.property
  · exact (smallCoefficient_symmetric 0 6 2 0).trans zero_6_cell_02.property
  · exact (smallCoefficient_symmetric 0 6 2 1).trans zero_6_cell_12.property
  · exact zero_6_cell_22.property
  · exact zero_6_cell_23.property
  · exact zero_6_cell_24.property
  · exact (smallCoefficient_symmetric 0 6 3 0).trans zero_6_cell_03.property
  · exact (smallCoefficient_symmetric 0 6 3 1).trans zero_6_cell_13.property
  · exact (smallCoefficient_symmetric 0 6 3 2).trans zero_6_cell_23.property
  · exact zero_6_cell_33.property
  · exact zero_6_cell_34.property
  · exact (smallCoefficient_symmetric 0 6 4 0).trans zero_6_cell_04.property
  · exact (smallCoefficient_symmetric 0 6 4 1).trans zero_6_cell_14.property
  · exact (smallCoefficient_symmetric 0 6 4 2).trans zero_6_cell_24.property
  · exact (smallCoefficient_symmetric 0 6 4 3).trans zero_6_cell_34.property
  · exact zero_6_cell_44.property

private theorem zero_6_first_pos : 0 < zero_6_matrix 0 0 := by
  dsimp only [zero_6_matrix,zero_6_cell_00,zero_6_cell_01,zero_6_cell_02,zero_6_cell_03,zero_6_cell_04,zero_6_cell_11,zero_6_cell_12,zero_6_cell_13,zero_6_cell_14,zero_6_cell_22,zero_6_cell_23,zero_6_cell_24,zero_6_cell_33,zero_6_cell_34,zero_6_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_6_delta_pos : 0 < delta zero_6_matrix := by
  dsimp only [zero_6_matrix,zero_6_cell_00,zero_6_cell_01,zero_6_cell_02,zero_6_cell_03,zero_6_cell_04,zero_6_cell_11,zero_6_cell_12,zero_6_cell_13,zero_6_cell_14,zero_6_cell_22,zero_6_cell_23,zero_6_cell_24,zero_6_cell_33,zero_6_cell_34,zero_6_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_6_schur_pos : 0 < schur zero_6_matrix 0 0 := by
  dsimp only [zero_6_matrix,zero_6_cell_00,zero_6_cell_01,zero_6_cell_02,zero_6_cell_03,zero_6_cell_04,zero_6_cell_11,zero_6_cell_12,zero_6_cell_13,zero_6_cell_14,zero_6_cell_22,zero_6_cell_23,zero_6_cell_24,zero_6_cell_33,zero_6_cell_34,zero_6_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_6_minor_pos : 0 < minor zero_6_matrix := by
  dsimp only [zero_6_matrix,zero_6_cell_00,zero_6_cell_01,zero_6_cell_02,zero_6_cell_03,zero_6_cell_04,zero_6_cell_11,zero_6_cell_12,zero_6_cell_13,zero_6_cell_14,zero_6_cell_22,zero_6_cell_23,zero_6_cell_24,zero_6_cell_33,zero_6_cell_34,zero_6_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_6_det_pos : 0 < determinant zero_6_matrix := by
  dsimp only [zero_6_matrix,zero_6_cell_00,zero_6_cell_01,zero_6_cell_02,zero_6_cell_03,zero_6_cell_04,zero_6_cell_11,zero_6_cell_12,zero_6_cell_13,zero_6_cell_14,zero_6_cell_22,zero_6_cell_23,zero_6_cell_24,zero_6_cell_33,zero_6_cell_34,zero_6_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_6_matrix_posDef : zero_6_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_6_first_pos zero_6_delta_pos zero_6_schur_pos
    zero_6_minor_pos zero_6_det_pos
  intro i j
  rw [← zero_6_matrix_eq]
  exact smallCoefficient_symmetric 0 6 i j

private theorem zero_6_posDef : (smallCoefficient 0 6).PosDef := by
  rw [zero_6_matrix_eq]
  exact zero_6_matrix_posDef


private def zero_7_moment_0 : {v : ℝ // momentCoefficient 0 7 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_7_moment_1 : {v : ℝ // momentCoefficient 0 7 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_7_moment_2 : {v : ℝ // momentCoefficient 0 7 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_7_moment_3 : {v : ℝ // momentCoefficient 0 7 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_7_moment_4 : {v : ℝ // momentCoefficient 0 7 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_7_moment_5 : {v : ℝ // momentCoefficient 0 7 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_7_moment_6 : {v : ℝ // momentCoefficient 0 7 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_7_moment_7 : {v : ℝ // momentCoefficient 0 7 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_7_moment_8 : {v : ℝ // momentCoefficient 0 7 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_7_cell_00 : {v : ℝ // smallCoefficient 0 7 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_7_moment_0.property]
      dsimp only [zero_7_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_01 : {v : ℝ // smallCoefficient 0 7 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_7_moment_0.property,zero_7_moment_1.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_02 : {v : ℝ // smallCoefficient 0 7 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_03 : {v : ℝ // smallCoefficient 0 7 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_04 : {v : ℝ // smallCoefficient 0 7 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property,zero_7_moment_4.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3,zero_7_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_11 : {v : ℝ // smallCoefficient 0 7 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_12 : {v : ℝ // smallCoefficient 0 7 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_13 : {v : ℝ // smallCoefficient 0 7 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property,zero_7_moment_4.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3,zero_7_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_14 : {v : ℝ // smallCoefficient 0 7 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property,zero_7_moment_4.property,zero_7_moment_5.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3,zero_7_moment_4,zero_7_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_22 : {v : ℝ // smallCoefficient 0 7 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property,zero_7_moment_4.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3,zero_7_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_23 : {v : ℝ // smallCoefficient 0 7 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property,zero_7_moment_4.property,zero_7_moment_5.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3,zero_7_moment_4,zero_7_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_24 : {v : ℝ // smallCoefficient 0 7 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property,zero_7_moment_4.property,zero_7_moment_5.property,zero_7_moment_6.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3,zero_7_moment_4,zero_7_moment_5,zero_7_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_33 : {v : ℝ // smallCoefficient 0 7 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property,zero_7_moment_4.property,zero_7_moment_5.property,zero_7_moment_6.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3,zero_7_moment_4,zero_7_moment_5,zero_7_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_34 : {v : ℝ // smallCoefficient 0 7 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property,zero_7_moment_4.property,zero_7_moment_5.property,zero_7_moment_6.property,zero_7_moment_7.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3,zero_7_moment_4,zero_7_moment_5,zero_7_moment_6,zero_7_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_cell_44 : {v : ℝ // smallCoefficient 0 7 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_7_moment_0.property,zero_7_moment_1.property,zero_7_moment_2.property,zero_7_moment_3.property,zero_7_moment_4.property,zero_7_moment_5.property,zero_7_moment_6.property,zero_7_moment_7.property,zero_7_moment_8.property]
      dsimp only [zero_7_moment_0,zero_7_moment_1,zero_7_moment_2,zero_7_moment_3,zero_7_moment_4,zero_7_moment_5,zero_7_moment_6,zero_7_moment_7,zero_7_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_7_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_7_cell_00.val,zero_7_cell_01.val,zero_7_cell_02.val,zero_7_cell_03.val,zero_7_cell_04.val],
    ![zero_7_cell_01.val,zero_7_cell_11.val,zero_7_cell_12.val,zero_7_cell_13.val,zero_7_cell_14.val],
    ![zero_7_cell_02.val,zero_7_cell_12.val,zero_7_cell_22.val,zero_7_cell_23.val,zero_7_cell_24.val],
    ![zero_7_cell_03.val,zero_7_cell_13.val,zero_7_cell_23.val,zero_7_cell_33.val,zero_7_cell_34.val],
    ![zero_7_cell_04.val,zero_7_cell_14.val,zero_7_cell_24.val,zero_7_cell_34.val,zero_7_cell_44.val]]

private theorem zero_7_matrix_eq : smallCoefficient 0 7=zero_7_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_7_cell_00.property
  · exact zero_7_cell_01.property
  · exact zero_7_cell_02.property
  · exact zero_7_cell_03.property
  · exact zero_7_cell_04.property
  · exact (smallCoefficient_symmetric 0 7 1 0).trans zero_7_cell_01.property
  · exact zero_7_cell_11.property
  · exact zero_7_cell_12.property
  · exact zero_7_cell_13.property
  · exact zero_7_cell_14.property
  · exact (smallCoefficient_symmetric 0 7 2 0).trans zero_7_cell_02.property
  · exact (smallCoefficient_symmetric 0 7 2 1).trans zero_7_cell_12.property
  · exact zero_7_cell_22.property
  · exact zero_7_cell_23.property
  · exact zero_7_cell_24.property
  · exact (smallCoefficient_symmetric 0 7 3 0).trans zero_7_cell_03.property
  · exact (smallCoefficient_symmetric 0 7 3 1).trans zero_7_cell_13.property
  · exact (smallCoefficient_symmetric 0 7 3 2).trans zero_7_cell_23.property
  · exact zero_7_cell_33.property
  · exact zero_7_cell_34.property
  · exact (smallCoefficient_symmetric 0 7 4 0).trans zero_7_cell_04.property
  · exact (smallCoefficient_symmetric 0 7 4 1).trans zero_7_cell_14.property
  · exact (smallCoefficient_symmetric 0 7 4 2).trans zero_7_cell_24.property
  · exact (smallCoefficient_symmetric 0 7 4 3).trans zero_7_cell_34.property
  · exact zero_7_cell_44.property

private theorem zero_7_first_pos : 0 < zero_7_matrix 0 0 := by
  dsimp only [zero_7_matrix,zero_7_cell_00,zero_7_cell_01,zero_7_cell_02,zero_7_cell_03,zero_7_cell_04,zero_7_cell_11,zero_7_cell_12,zero_7_cell_13,zero_7_cell_14,zero_7_cell_22,zero_7_cell_23,zero_7_cell_24,zero_7_cell_33,zero_7_cell_34,zero_7_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_7_delta_pos : 0 < delta zero_7_matrix := by
  dsimp only [zero_7_matrix,zero_7_cell_00,zero_7_cell_01,zero_7_cell_02,zero_7_cell_03,zero_7_cell_04,zero_7_cell_11,zero_7_cell_12,zero_7_cell_13,zero_7_cell_14,zero_7_cell_22,zero_7_cell_23,zero_7_cell_24,zero_7_cell_33,zero_7_cell_34,zero_7_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_7_schur_pos : 0 < schur zero_7_matrix 0 0 := by
  dsimp only [zero_7_matrix,zero_7_cell_00,zero_7_cell_01,zero_7_cell_02,zero_7_cell_03,zero_7_cell_04,zero_7_cell_11,zero_7_cell_12,zero_7_cell_13,zero_7_cell_14,zero_7_cell_22,zero_7_cell_23,zero_7_cell_24,zero_7_cell_33,zero_7_cell_34,zero_7_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_7_minor_pos : 0 < minor zero_7_matrix := by
  dsimp only [zero_7_matrix,zero_7_cell_00,zero_7_cell_01,zero_7_cell_02,zero_7_cell_03,zero_7_cell_04,zero_7_cell_11,zero_7_cell_12,zero_7_cell_13,zero_7_cell_14,zero_7_cell_22,zero_7_cell_23,zero_7_cell_24,zero_7_cell_33,zero_7_cell_34,zero_7_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_7_det_pos : 0 < determinant zero_7_matrix := by
  dsimp only [zero_7_matrix,zero_7_cell_00,zero_7_cell_01,zero_7_cell_02,zero_7_cell_03,zero_7_cell_04,zero_7_cell_11,zero_7_cell_12,zero_7_cell_13,zero_7_cell_14,zero_7_cell_22,zero_7_cell_23,zero_7_cell_24,zero_7_cell_33,zero_7_cell_34,zero_7_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_7_matrix_posDef : zero_7_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_7_first_pos zero_7_delta_pos zero_7_schur_pos
    zero_7_minor_pos zero_7_det_pos
  intro i j
  rw [← zero_7_matrix_eq]
  exact smallCoefficient_symmetric 0 7 i j

private theorem zero_7_posDef : (smallCoefficient 0 7).PosDef := by
  rw [zero_7_matrix_eq]
  exact zero_7_matrix_posDef


private def zero_8_moment_0 : {v : ℝ // momentCoefficient 0 8 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_8_moment_1 : {v : ℝ // momentCoefficient 0 8 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_8_moment_2 : {v : ℝ // momentCoefficient 0 8 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_8_moment_3 : {v : ℝ // momentCoefficient 0 8 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_8_moment_4 : {v : ℝ // momentCoefficient 0 8 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_8_moment_5 : {v : ℝ // momentCoefficient 0 8 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_8_moment_6 : {v : ℝ // momentCoefficient 0 8 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_8_moment_7 : {v : ℝ // momentCoefficient 0 8 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_8_moment_8 : {v : ℝ // momentCoefficient 0 8 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_8_cell_00 : {v : ℝ // smallCoefficient 0 8 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_8_moment_0.property]
      dsimp only [zero_8_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_01 : {v : ℝ // smallCoefficient 0 8 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_8_moment_0.property,zero_8_moment_1.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_02 : {v : ℝ // smallCoefficient 0 8 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_03 : {v : ℝ // smallCoefficient 0 8 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_04 : {v : ℝ // smallCoefficient 0 8 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property,zero_8_moment_4.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3,zero_8_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_11 : {v : ℝ // smallCoefficient 0 8 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_12 : {v : ℝ // smallCoefficient 0 8 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_13 : {v : ℝ // smallCoefficient 0 8 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property,zero_8_moment_4.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3,zero_8_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_14 : {v : ℝ // smallCoefficient 0 8 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property,zero_8_moment_4.property,zero_8_moment_5.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3,zero_8_moment_4,zero_8_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_22 : {v : ℝ // smallCoefficient 0 8 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property,zero_8_moment_4.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3,zero_8_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_23 : {v : ℝ // smallCoefficient 0 8 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property,zero_8_moment_4.property,zero_8_moment_5.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3,zero_8_moment_4,zero_8_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_24 : {v : ℝ // smallCoefficient 0 8 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property,zero_8_moment_4.property,zero_8_moment_5.property,zero_8_moment_6.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3,zero_8_moment_4,zero_8_moment_5,zero_8_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_33 : {v : ℝ // smallCoefficient 0 8 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property,zero_8_moment_4.property,zero_8_moment_5.property,zero_8_moment_6.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3,zero_8_moment_4,zero_8_moment_5,zero_8_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_34 : {v : ℝ // smallCoefficient 0 8 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property,zero_8_moment_4.property,zero_8_moment_5.property,zero_8_moment_6.property,zero_8_moment_7.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3,zero_8_moment_4,zero_8_moment_5,zero_8_moment_6,zero_8_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_cell_44 : {v : ℝ // smallCoefficient 0 8 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_8_moment_0.property,zero_8_moment_1.property,zero_8_moment_2.property,zero_8_moment_3.property,zero_8_moment_4.property,zero_8_moment_5.property,zero_8_moment_6.property,zero_8_moment_7.property,zero_8_moment_8.property]
      dsimp only [zero_8_moment_0,zero_8_moment_1,zero_8_moment_2,zero_8_moment_3,zero_8_moment_4,zero_8_moment_5,zero_8_moment_6,zero_8_moment_7,zero_8_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_8_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_8_cell_00.val,zero_8_cell_01.val,zero_8_cell_02.val,zero_8_cell_03.val,zero_8_cell_04.val],
    ![zero_8_cell_01.val,zero_8_cell_11.val,zero_8_cell_12.val,zero_8_cell_13.val,zero_8_cell_14.val],
    ![zero_8_cell_02.val,zero_8_cell_12.val,zero_8_cell_22.val,zero_8_cell_23.val,zero_8_cell_24.val],
    ![zero_8_cell_03.val,zero_8_cell_13.val,zero_8_cell_23.val,zero_8_cell_33.val,zero_8_cell_34.val],
    ![zero_8_cell_04.val,zero_8_cell_14.val,zero_8_cell_24.val,zero_8_cell_34.val,zero_8_cell_44.val]]

private theorem zero_8_matrix_eq : smallCoefficient 0 8=zero_8_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_8_cell_00.property
  · exact zero_8_cell_01.property
  · exact zero_8_cell_02.property
  · exact zero_8_cell_03.property
  · exact zero_8_cell_04.property
  · exact (smallCoefficient_symmetric 0 8 1 0).trans zero_8_cell_01.property
  · exact zero_8_cell_11.property
  · exact zero_8_cell_12.property
  · exact zero_8_cell_13.property
  · exact zero_8_cell_14.property
  · exact (smallCoefficient_symmetric 0 8 2 0).trans zero_8_cell_02.property
  · exact (smallCoefficient_symmetric 0 8 2 1).trans zero_8_cell_12.property
  · exact zero_8_cell_22.property
  · exact zero_8_cell_23.property
  · exact zero_8_cell_24.property
  · exact (smallCoefficient_symmetric 0 8 3 0).trans zero_8_cell_03.property
  · exact (smallCoefficient_symmetric 0 8 3 1).trans zero_8_cell_13.property
  · exact (smallCoefficient_symmetric 0 8 3 2).trans zero_8_cell_23.property
  · exact zero_8_cell_33.property
  · exact zero_8_cell_34.property
  · exact (smallCoefficient_symmetric 0 8 4 0).trans zero_8_cell_04.property
  · exact (smallCoefficient_symmetric 0 8 4 1).trans zero_8_cell_14.property
  · exact (smallCoefficient_symmetric 0 8 4 2).trans zero_8_cell_24.property
  · exact (smallCoefficient_symmetric 0 8 4 3).trans zero_8_cell_34.property
  · exact zero_8_cell_44.property

private theorem zero_8_first_pos : 0 < zero_8_matrix 0 0 := by
  dsimp only [zero_8_matrix,zero_8_cell_00,zero_8_cell_01,zero_8_cell_02,zero_8_cell_03,zero_8_cell_04,zero_8_cell_11,zero_8_cell_12,zero_8_cell_13,zero_8_cell_14,zero_8_cell_22,zero_8_cell_23,zero_8_cell_24,zero_8_cell_33,zero_8_cell_34,zero_8_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_8_delta_pos : 0 < delta zero_8_matrix := by
  dsimp only [zero_8_matrix,zero_8_cell_00,zero_8_cell_01,zero_8_cell_02,zero_8_cell_03,zero_8_cell_04,zero_8_cell_11,zero_8_cell_12,zero_8_cell_13,zero_8_cell_14,zero_8_cell_22,zero_8_cell_23,zero_8_cell_24,zero_8_cell_33,zero_8_cell_34,zero_8_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_8_schur_pos : 0 < schur zero_8_matrix 0 0 := by
  dsimp only [zero_8_matrix,zero_8_cell_00,zero_8_cell_01,zero_8_cell_02,zero_8_cell_03,zero_8_cell_04,zero_8_cell_11,zero_8_cell_12,zero_8_cell_13,zero_8_cell_14,zero_8_cell_22,zero_8_cell_23,zero_8_cell_24,zero_8_cell_33,zero_8_cell_34,zero_8_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_8_minor_pos : 0 < minor zero_8_matrix := by
  dsimp only [zero_8_matrix,zero_8_cell_00,zero_8_cell_01,zero_8_cell_02,zero_8_cell_03,zero_8_cell_04,zero_8_cell_11,zero_8_cell_12,zero_8_cell_13,zero_8_cell_14,zero_8_cell_22,zero_8_cell_23,zero_8_cell_24,zero_8_cell_33,zero_8_cell_34,zero_8_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_8_det_pos : 0 < determinant zero_8_matrix := by
  dsimp only [zero_8_matrix,zero_8_cell_00,zero_8_cell_01,zero_8_cell_02,zero_8_cell_03,zero_8_cell_04,zero_8_cell_11,zero_8_cell_12,zero_8_cell_13,zero_8_cell_14,zero_8_cell_22,zero_8_cell_23,zero_8_cell_24,zero_8_cell_33,zero_8_cell_34,zero_8_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_8_matrix_posDef : zero_8_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_8_first_pos zero_8_delta_pos zero_8_schur_pos
    zero_8_minor_pos zero_8_det_pos
  intro i j
  rw [← zero_8_matrix_eq]
  exact smallCoefficient_symmetric 0 8 i j

private theorem zero_8_posDef : (smallCoefficient 0 8).PosDef := by
  rw [zero_8_matrix_eq]
  exact zero_8_matrix_posDef


private def zero_9_moment_0 : {v : ℝ // momentCoefficient 0 9 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_9_moment_1 : {v : ℝ // momentCoefficient 0 9 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_9_moment_2 : {v : ℝ // momentCoefficient 0 9 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_9_moment_3 : {v : ℝ // momentCoefficient 0 9 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_9_moment_4 : {v : ℝ // momentCoefficient 0 9 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_9_moment_5 : {v : ℝ // momentCoefficient 0 9 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_9_moment_6 : {v : ℝ // momentCoefficient 0 9 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_9_moment_7 : {v : ℝ // momentCoefficient 0 9 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_9_moment_8 : {v : ℝ // momentCoefficient 0 9 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_9_cell_00 : {v : ℝ // smallCoefficient 0 9 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_9_moment_0.property]
      dsimp only [zero_9_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_01 : {v : ℝ // smallCoefficient 0 9 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_9_moment_0.property,zero_9_moment_1.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_02 : {v : ℝ // smallCoefficient 0 9 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_03 : {v : ℝ // smallCoefficient 0 9 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_04 : {v : ℝ // smallCoefficient 0 9 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property,zero_9_moment_4.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3,zero_9_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_11 : {v : ℝ // smallCoefficient 0 9 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_12 : {v : ℝ // smallCoefficient 0 9 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_13 : {v : ℝ // smallCoefficient 0 9 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property,zero_9_moment_4.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3,zero_9_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_14 : {v : ℝ // smallCoefficient 0 9 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property,zero_9_moment_4.property,zero_9_moment_5.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3,zero_9_moment_4,zero_9_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_22 : {v : ℝ // smallCoefficient 0 9 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property,zero_9_moment_4.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3,zero_9_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_23 : {v : ℝ // smallCoefficient 0 9 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property,zero_9_moment_4.property,zero_9_moment_5.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3,zero_9_moment_4,zero_9_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_24 : {v : ℝ // smallCoefficient 0 9 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property,zero_9_moment_4.property,zero_9_moment_5.property,zero_9_moment_6.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3,zero_9_moment_4,zero_9_moment_5,zero_9_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_33 : {v : ℝ // smallCoefficient 0 9 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property,zero_9_moment_4.property,zero_9_moment_5.property,zero_9_moment_6.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3,zero_9_moment_4,zero_9_moment_5,zero_9_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_34 : {v : ℝ // smallCoefficient 0 9 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property,zero_9_moment_4.property,zero_9_moment_5.property,zero_9_moment_6.property,zero_9_moment_7.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3,zero_9_moment_4,zero_9_moment_5,zero_9_moment_6,zero_9_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_cell_44 : {v : ℝ // smallCoefficient 0 9 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_9_moment_0.property,zero_9_moment_1.property,zero_9_moment_2.property,zero_9_moment_3.property,zero_9_moment_4.property,zero_9_moment_5.property,zero_9_moment_6.property,zero_9_moment_7.property,zero_9_moment_8.property]
      dsimp only [zero_9_moment_0,zero_9_moment_1,zero_9_moment_2,zero_9_moment_3,zero_9_moment_4,zero_9_moment_5,zero_9_moment_6,zero_9_moment_7,zero_9_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_9_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_9_cell_00.val,zero_9_cell_01.val,zero_9_cell_02.val,zero_9_cell_03.val,zero_9_cell_04.val],
    ![zero_9_cell_01.val,zero_9_cell_11.val,zero_9_cell_12.val,zero_9_cell_13.val,zero_9_cell_14.val],
    ![zero_9_cell_02.val,zero_9_cell_12.val,zero_9_cell_22.val,zero_9_cell_23.val,zero_9_cell_24.val],
    ![zero_9_cell_03.val,zero_9_cell_13.val,zero_9_cell_23.val,zero_9_cell_33.val,zero_9_cell_34.val],
    ![zero_9_cell_04.val,zero_9_cell_14.val,zero_9_cell_24.val,zero_9_cell_34.val,zero_9_cell_44.val]]

private theorem zero_9_matrix_eq : smallCoefficient 0 9=zero_9_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_9_cell_00.property
  · exact zero_9_cell_01.property
  · exact zero_9_cell_02.property
  · exact zero_9_cell_03.property
  · exact zero_9_cell_04.property
  · exact (smallCoefficient_symmetric 0 9 1 0).trans zero_9_cell_01.property
  · exact zero_9_cell_11.property
  · exact zero_9_cell_12.property
  · exact zero_9_cell_13.property
  · exact zero_9_cell_14.property
  · exact (smallCoefficient_symmetric 0 9 2 0).trans zero_9_cell_02.property
  · exact (smallCoefficient_symmetric 0 9 2 1).trans zero_9_cell_12.property
  · exact zero_9_cell_22.property
  · exact zero_9_cell_23.property
  · exact zero_9_cell_24.property
  · exact (smallCoefficient_symmetric 0 9 3 0).trans zero_9_cell_03.property
  · exact (smallCoefficient_symmetric 0 9 3 1).trans zero_9_cell_13.property
  · exact (smallCoefficient_symmetric 0 9 3 2).trans zero_9_cell_23.property
  · exact zero_9_cell_33.property
  · exact zero_9_cell_34.property
  · exact (smallCoefficient_symmetric 0 9 4 0).trans zero_9_cell_04.property
  · exact (smallCoefficient_symmetric 0 9 4 1).trans zero_9_cell_14.property
  · exact (smallCoefficient_symmetric 0 9 4 2).trans zero_9_cell_24.property
  · exact (smallCoefficient_symmetric 0 9 4 3).trans zero_9_cell_34.property
  · exact zero_9_cell_44.property

private theorem zero_9_first_pos : 0 < zero_9_matrix 0 0 := by
  dsimp only [zero_9_matrix,zero_9_cell_00,zero_9_cell_01,zero_9_cell_02,zero_9_cell_03,zero_9_cell_04,zero_9_cell_11,zero_9_cell_12,zero_9_cell_13,zero_9_cell_14,zero_9_cell_22,zero_9_cell_23,zero_9_cell_24,zero_9_cell_33,zero_9_cell_34,zero_9_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_9_delta_pos : 0 < delta zero_9_matrix := by
  dsimp only [zero_9_matrix,zero_9_cell_00,zero_9_cell_01,zero_9_cell_02,zero_9_cell_03,zero_9_cell_04,zero_9_cell_11,zero_9_cell_12,zero_9_cell_13,zero_9_cell_14,zero_9_cell_22,zero_9_cell_23,zero_9_cell_24,zero_9_cell_33,zero_9_cell_34,zero_9_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_9_schur_pos : 0 < schur zero_9_matrix 0 0 := by
  dsimp only [zero_9_matrix,zero_9_cell_00,zero_9_cell_01,zero_9_cell_02,zero_9_cell_03,zero_9_cell_04,zero_9_cell_11,zero_9_cell_12,zero_9_cell_13,zero_9_cell_14,zero_9_cell_22,zero_9_cell_23,zero_9_cell_24,zero_9_cell_33,zero_9_cell_34,zero_9_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_9_minor_pos : 0 < minor zero_9_matrix := by
  dsimp only [zero_9_matrix,zero_9_cell_00,zero_9_cell_01,zero_9_cell_02,zero_9_cell_03,zero_9_cell_04,zero_9_cell_11,zero_9_cell_12,zero_9_cell_13,zero_9_cell_14,zero_9_cell_22,zero_9_cell_23,zero_9_cell_24,zero_9_cell_33,zero_9_cell_34,zero_9_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_9_det_pos : 0 < determinant zero_9_matrix := by
  dsimp only [zero_9_matrix,zero_9_cell_00,zero_9_cell_01,zero_9_cell_02,zero_9_cell_03,zero_9_cell_04,zero_9_cell_11,zero_9_cell_12,zero_9_cell_13,zero_9_cell_14,zero_9_cell_22,zero_9_cell_23,zero_9_cell_24,zero_9_cell_33,zero_9_cell_34,zero_9_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_9_matrix_posDef : zero_9_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_9_first_pos zero_9_delta_pos zero_9_schur_pos
    zero_9_minor_pos zero_9_det_pos
  intro i j
  rw [← zero_9_matrix_eq]
  exact smallCoefficient_symmetric 0 9 i j

private theorem zero_9_posDef : (smallCoefficient 0 9).PosDef := by
  rw [zero_9_matrix_eq]
  exact zero_9_matrix_posDef


private def zero_10_moment_0 : {v : ℝ // momentCoefficient 0 10 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_10_moment_1 : {v : ℝ // momentCoefficient 0 10 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_10_moment_2 : {v : ℝ // momentCoefficient 0 10 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_10_moment_3 : {v : ℝ // momentCoefficient 0 10 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_10_moment_4 : {v : ℝ // momentCoefficient 0 10 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_10_moment_5 : {v : ℝ // momentCoefficient 0 10 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_10_moment_6 : {v : ℝ // momentCoefficient 0 10 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_10_moment_7 : {v : ℝ // momentCoefficient 0 10 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_10_moment_8 : {v : ℝ // momentCoefficient 0 10 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_10_cell_00 : {v : ℝ // smallCoefficient 0 10 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_10_moment_0.property]
      dsimp only [zero_10_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_01 : {v : ℝ // smallCoefficient 0 10 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_10_moment_0.property,zero_10_moment_1.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_02 : {v : ℝ // smallCoefficient 0 10 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_03 : {v : ℝ // smallCoefficient 0 10 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_04 : {v : ℝ // smallCoefficient 0 10 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property,zero_10_moment_4.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3,zero_10_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_11 : {v : ℝ // smallCoefficient 0 10 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_12 : {v : ℝ // smallCoefficient 0 10 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_13 : {v : ℝ // smallCoefficient 0 10 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property,zero_10_moment_4.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3,zero_10_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_14 : {v : ℝ // smallCoefficient 0 10 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property,zero_10_moment_4.property,zero_10_moment_5.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3,zero_10_moment_4,zero_10_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_22 : {v : ℝ // smallCoefficient 0 10 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property,zero_10_moment_4.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3,zero_10_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_23 : {v : ℝ // smallCoefficient 0 10 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property,zero_10_moment_4.property,zero_10_moment_5.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3,zero_10_moment_4,zero_10_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_24 : {v : ℝ // smallCoefficient 0 10 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property,zero_10_moment_4.property,zero_10_moment_5.property,zero_10_moment_6.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3,zero_10_moment_4,zero_10_moment_5,zero_10_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_33 : {v : ℝ // smallCoefficient 0 10 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property,zero_10_moment_4.property,zero_10_moment_5.property,zero_10_moment_6.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3,zero_10_moment_4,zero_10_moment_5,zero_10_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_34 : {v : ℝ // smallCoefficient 0 10 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property,zero_10_moment_4.property,zero_10_moment_5.property,zero_10_moment_6.property,zero_10_moment_7.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3,zero_10_moment_4,zero_10_moment_5,zero_10_moment_6,zero_10_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_cell_44 : {v : ℝ // smallCoefficient 0 10 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_10_moment_0.property,zero_10_moment_1.property,zero_10_moment_2.property,zero_10_moment_3.property,zero_10_moment_4.property,zero_10_moment_5.property,zero_10_moment_6.property,zero_10_moment_7.property,zero_10_moment_8.property]
      dsimp only [zero_10_moment_0,zero_10_moment_1,zero_10_moment_2,zero_10_moment_3,zero_10_moment_4,zero_10_moment_5,zero_10_moment_6,zero_10_moment_7,zero_10_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_10_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_10_cell_00.val,zero_10_cell_01.val,zero_10_cell_02.val,zero_10_cell_03.val,zero_10_cell_04.val],
    ![zero_10_cell_01.val,zero_10_cell_11.val,zero_10_cell_12.val,zero_10_cell_13.val,zero_10_cell_14.val],
    ![zero_10_cell_02.val,zero_10_cell_12.val,zero_10_cell_22.val,zero_10_cell_23.val,zero_10_cell_24.val],
    ![zero_10_cell_03.val,zero_10_cell_13.val,zero_10_cell_23.val,zero_10_cell_33.val,zero_10_cell_34.val],
    ![zero_10_cell_04.val,zero_10_cell_14.val,zero_10_cell_24.val,zero_10_cell_34.val,zero_10_cell_44.val]]

private theorem zero_10_matrix_eq : smallCoefficient 0 10=zero_10_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_10_cell_00.property
  · exact zero_10_cell_01.property
  · exact zero_10_cell_02.property
  · exact zero_10_cell_03.property
  · exact zero_10_cell_04.property
  · exact (smallCoefficient_symmetric 0 10 1 0).trans zero_10_cell_01.property
  · exact zero_10_cell_11.property
  · exact zero_10_cell_12.property
  · exact zero_10_cell_13.property
  · exact zero_10_cell_14.property
  · exact (smallCoefficient_symmetric 0 10 2 0).trans zero_10_cell_02.property
  · exact (smallCoefficient_symmetric 0 10 2 1).trans zero_10_cell_12.property
  · exact zero_10_cell_22.property
  · exact zero_10_cell_23.property
  · exact zero_10_cell_24.property
  · exact (smallCoefficient_symmetric 0 10 3 0).trans zero_10_cell_03.property
  · exact (smallCoefficient_symmetric 0 10 3 1).trans zero_10_cell_13.property
  · exact (smallCoefficient_symmetric 0 10 3 2).trans zero_10_cell_23.property
  · exact zero_10_cell_33.property
  · exact zero_10_cell_34.property
  · exact (smallCoefficient_symmetric 0 10 4 0).trans zero_10_cell_04.property
  · exact (smallCoefficient_symmetric 0 10 4 1).trans zero_10_cell_14.property
  · exact (smallCoefficient_symmetric 0 10 4 2).trans zero_10_cell_24.property
  · exact (smallCoefficient_symmetric 0 10 4 3).trans zero_10_cell_34.property
  · exact zero_10_cell_44.property

private theorem zero_10_first_pos : 0 < zero_10_matrix 0 0 := by
  dsimp only [zero_10_matrix,zero_10_cell_00,zero_10_cell_01,zero_10_cell_02,zero_10_cell_03,zero_10_cell_04,zero_10_cell_11,zero_10_cell_12,zero_10_cell_13,zero_10_cell_14,zero_10_cell_22,zero_10_cell_23,zero_10_cell_24,zero_10_cell_33,zero_10_cell_34,zero_10_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_10_delta_pos : 0 < delta zero_10_matrix := by
  dsimp only [zero_10_matrix,zero_10_cell_00,zero_10_cell_01,zero_10_cell_02,zero_10_cell_03,zero_10_cell_04,zero_10_cell_11,zero_10_cell_12,zero_10_cell_13,zero_10_cell_14,zero_10_cell_22,zero_10_cell_23,zero_10_cell_24,zero_10_cell_33,zero_10_cell_34,zero_10_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_10_schur_pos : 0 < schur zero_10_matrix 0 0 := by
  dsimp only [zero_10_matrix,zero_10_cell_00,zero_10_cell_01,zero_10_cell_02,zero_10_cell_03,zero_10_cell_04,zero_10_cell_11,zero_10_cell_12,zero_10_cell_13,zero_10_cell_14,zero_10_cell_22,zero_10_cell_23,zero_10_cell_24,zero_10_cell_33,zero_10_cell_34,zero_10_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_10_minor_pos : 0 < minor zero_10_matrix := by
  dsimp only [zero_10_matrix,zero_10_cell_00,zero_10_cell_01,zero_10_cell_02,zero_10_cell_03,zero_10_cell_04,zero_10_cell_11,zero_10_cell_12,zero_10_cell_13,zero_10_cell_14,zero_10_cell_22,zero_10_cell_23,zero_10_cell_24,zero_10_cell_33,zero_10_cell_34,zero_10_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_10_det_pos : 0 < determinant zero_10_matrix := by
  dsimp only [zero_10_matrix,zero_10_cell_00,zero_10_cell_01,zero_10_cell_02,zero_10_cell_03,zero_10_cell_04,zero_10_cell_11,zero_10_cell_12,zero_10_cell_13,zero_10_cell_14,zero_10_cell_22,zero_10_cell_23,zero_10_cell_24,zero_10_cell_33,zero_10_cell_34,zero_10_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_10_matrix_posDef : zero_10_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_10_first_pos zero_10_delta_pos zero_10_schur_pos
    zero_10_minor_pos zero_10_det_pos
  intro i j
  rw [← zero_10_matrix_eq]
  exact smallCoefficient_symmetric 0 10 i j

private theorem zero_10_posDef : (smallCoefficient 0 10).PosDef := by
  rw [zero_10_matrix_eq]
  exact zero_10_matrix_posDef


private def zero_11_moment_0 : {v : ℝ // momentCoefficient 0 11 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_11_moment_1 : {v : ℝ // momentCoefficient 0 11 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_11_moment_2 : {v : ℝ // momentCoefficient 0 11 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_11_moment_3 : {v : ℝ // momentCoefficient 0 11 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_11_moment_4 : {v : ℝ // momentCoefficient 0 11 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_11_moment_5 : {v : ℝ // momentCoefficient 0 11 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_11_moment_6 : {v : ℝ // momentCoefficient 0 11 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_11_moment_7 : {v : ℝ // momentCoefficient 0 11 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_11_moment_8 : {v : ℝ // momentCoefficient 0 11 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_11_cell_00 : {v : ℝ // smallCoefficient 0 11 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_11_moment_0.property]
      dsimp only [zero_11_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_01 : {v : ℝ // smallCoefficient 0 11 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_11_moment_0.property,zero_11_moment_1.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_02 : {v : ℝ // smallCoefficient 0 11 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_03 : {v : ℝ // smallCoefficient 0 11 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_04 : {v : ℝ // smallCoefficient 0 11 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property,zero_11_moment_4.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3,zero_11_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_11 : {v : ℝ // smallCoefficient 0 11 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_12 : {v : ℝ // smallCoefficient 0 11 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_13 : {v : ℝ // smallCoefficient 0 11 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property,zero_11_moment_4.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3,zero_11_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_14 : {v : ℝ // smallCoefficient 0 11 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property,zero_11_moment_4.property,zero_11_moment_5.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3,zero_11_moment_4,zero_11_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_22 : {v : ℝ // smallCoefficient 0 11 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property,zero_11_moment_4.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3,zero_11_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_23 : {v : ℝ // smallCoefficient 0 11 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property,zero_11_moment_4.property,zero_11_moment_5.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3,zero_11_moment_4,zero_11_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_24 : {v : ℝ // smallCoefficient 0 11 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property,zero_11_moment_4.property,zero_11_moment_5.property,zero_11_moment_6.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3,zero_11_moment_4,zero_11_moment_5,zero_11_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_33 : {v : ℝ // smallCoefficient 0 11 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property,zero_11_moment_4.property,zero_11_moment_5.property,zero_11_moment_6.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3,zero_11_moment_4,zero_11_moment_5,zero_11_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_34 : {v : ℝ // smallCoefficient 0 11 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property,zero_11_moment_4.property,zero_11_moment_5.property,zero_11_moment_6.property,zero_11_moment_7.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3,zero_11_moment_4,zero_11_moment_5,zero_11_moment_6,zero_11_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_cell_44 : {v : ℝ // smallCoefficient 0 11 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_11_moment_0.property,zero_11_moment_1.property,zero_11_moment_2.property,zero_11_moment_3.property,zero_11_moment_4.property,zero_11_moment_5.property,zero_11_moment_6.property,zero_11_moment_7.property,zero_11_moment_8.property]
      dsimp only [zero_11_moment_0,zero_11_moment_1,zero_11_moment_2,zero_11_moment_3,zero_11_moment_4,zero_11_moment_5,zero_11_moment_6,zero_11_moment_7,zero_11_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_11_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_11_cell_00.val,zero_11_cell_01.val,zero_11_cell_02.val,zero_11_cell_03.val,zero_11_cell_04.val],
    ![zero_11_cell_01.val,zero_11_cell_11.val,zero_11_cell_12.val,zero_11_cell_13.val,zero_11_cell_14.val],
    ![zero_11_cell_02.val,zero_11_cell_12.val,zero_11_cell_22.val,zero_11_cell_23.val,zero_11_cell_24.val],
    ![zero_11_cell_03.val,zero_11_cell_13.val,zero_11_cell_23.val,zero_11_cell_33.val,zero_11_cell_34.val],
    ![zero_11_cell_04.val,zero_11_cell_14.val,zero_11_cell_24.val,zero_11_cell_34.val,zero_11_cell_44.val]]

private theorem zero_11_matrix_eq : smallCoefficient 0 11=zero_11_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_11_cell_00.property
  · exact zero_11_cell_01.property
  · exact zero_11_cell_02.property
  · exact zero_11_cell_03.property
  · exact zero_11_cell_04.property
  · exact (smallCoefficient_symmetric 0 11 1 0).trans zero_11_cell_01.property
  · exact zero_11_cell_11.property
  · exact zero_11_cell_12.property
  · exact zero_11_cell_13.property
  · exact zero_11_cell_14.property
  · exact (smallCoefficient_symmetric 0 11 2 0).trans zero_11_cell_02.property
  · exact (smallCoefficient_symmetric 0 11 2 1).trans zero_11_cell_12.property
  · exact zero_11_cell_22.property
  · exact zero_11_cell_23.property
  · exact zero_11_cell_24.property
  · exact (smallCoefficient_symmetric 0 11 3 0).trans zero_11_cell_03.property
  · exact (smallCoefficient_symmetric 0 11 3 1).trans zero_11_cell_13.property
  · exact (smallCoefficient_symmetric 0 11 3 2).trans zero_11_cell_23.property
  · exact zero_11_cell_33.property
  · exact zero_11_cell_34.property
  · exact (smallCoefficient_symmetric 0 11 4 0).trans zero_11_cell_04.property
  · exact (smallCoefficient_symmetric 0 11 4 1).trans zero_11_cell_14.property
  · exact (smallCoefficient_symmetric 0 11 4 2).trans zero_11_cell_24.property
  · exact (smallCoefficient_symmetric 0 11 4 3).trans zero_11_cell_34.property
  · exact zero_11_cell_44.property

private theorem zero_11_first_pos : 0 < zero_11_matrix 0 0 := by
  dsimp only [zero_11_matrix,zero_11_cell_00,zero_11_cell_01,zero_11_cell_02,zero_11_cell_03,zero_11_cell_04,zero_11_cell_11,zero_11_cell_12,zero_11_cell_13,zero_11_cell_14,zero_11_cell_22,zero_11_cell_23,zero_11_cell_24,zero_11_cell_33,zero_11_cell_34,zero_11_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_11_delta_pos : 0 < delta zero_11_matrix := by
  dsimp only [zero_11_matrix,zero_11_cell_00,zero_11_cell_01,zero_11_cell_02,zero_11_cell_03,zero_11_cell_04,zero_11_cell_11,zero_11_cell_12,zero_11_cell_13,zero_11_cell_14,zero_11_cell_22,zero_11_cell_23,zero_11_cell_24,zero_11_cell_33,zero_11_cell_34,zero_11_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_11_schur_pos : 0 < schur zero_11_matrix 0 0 := by
  dsimp only [zero_11_matrix,zero_11_cell_00,zero_11_cell_01,zero_11_cell_02,zero_11_cell_03,zero_11_cell_04,zero_11_cell_11,zero_11_cell_12,zero_11_cell_13,zero_11_cell_14,zero_11_cell_22,zero_11_cell_23,zero_11_cell_24,zero_11_cell_33,zero_11_cell_34,zero_11_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_11_minor_pos : 0 < minor zero_11_matrix := by
  dsimp only [zero_11_matrix,zero_11_cell_00,zero_11_cell_01,zero_11_cell_02,zero_11_cell_03,zero_11_cell_04,zero_11_cell_11,zero_11_cell_12,zero_11_cell_13,zero_11_cell_14,zero_11_cell_22,zero_11_cell_23,zero_11_cell_24,zero_11_cell_33,zero_11_cell_34,zero_11_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_11_det_pos : 0 < determinant zero_11_matrix := by
  dsimp only [zero_11_matrix,zero_11_cell_00,zero_11_cell_01,zero_11_cell_02,zero_11_cell_03,zero_11_cell_04,zero_11_cell_11,zero_11_cell_12,zero_11_cell_13,zero_11_cell_14,zero_11_cell_22,zero_11_cell_23,zero_11_cell_24,zero_11_cell_33,zero_11_cell_34,zero_11_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_11_matrix_posDef : zero_11_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_11_first_pos zero_11_delta_pos zero_11_schur_pos
    zero_11_minor_pos zero_11_det_pos
  intro i j
  rw [← zero_11_matrix_eq]
  exact smallCoefficient_symmetric 0 11 i j

private theorem zero_11_posDef : (smallCoefficient 0 11).PosDef := by
  rw [zero_11_matrix_eq]
  exact zero_11_matrix_posDef


private def zero_12_moment_0 : {v : ℝ // momentCoefficient 0 12 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_12_moment_1 : {v : ℝ // momentCoefficient 0 12 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_12_moment_2 : {v : ℝ // momentCoefficient 0 12 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_12_moment_3 : {v : ℝ // momentCoefficient 0 12 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_12_moment_4 : {v : ℝ // momentCoefficient 0 12 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_12_moment_5 : {v : ℝ // momentCoefficient 0 12 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_12_moment_6 : {v : ℝ // momentCoefficient 0 12 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_12_moment_7 : {v : ℝ // momentCoefficient 0 12 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_12_moment_8 : {v : ℝ // momentCoefficient 0 12 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_12_cell_00 : {v : ℝ // smallCoefficient 0 12 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_12_moment_0.property]
      dsimp only [zero_12_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_01 : {v : ℝ // smallCoefficient 0 12 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_12_moment_0.property,zero_12_moment_1.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_02 : {v : ℝ // smallCoefficient 0 12 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_03 : {v : ℝ // smallCoefficient 0 12 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_04 : {v : ℝ // smallCoefficient 0 12 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property,zero_12_moment_4.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3,zero_12_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_11 : {v : ℝ // smallCoefficient 0 12 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_12 : {v : ℝ // smallCoefficient 0 12 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_13 : {v : ℝ // smallCoefficient 0 12 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property,zero_12_moment_4.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3,zero_12_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_14 : {v : ℝ // smallCoefficient 0 12 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property,zero_12_moment_4.property,zero_12_moment_5.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3,zero_12_moment_4,zero_12_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_22 : {v : ℝ // smallCoefficient 0 12 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property,zero_12_moment_4.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3,zero_12_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_23 : {v : ℝ // smallCoefficient 0 12 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property,zero_12_moment_4.property,zero_12_moment_5.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3,zero_12_moment_4,zero_12_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_24 : {v : ℝ // smallCoefficient 0 12 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property,zero_12_moment_4.property,zero_12_moment_5.property,zero_12_moment_6.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3,zero_12_moment_4,zero_12_moment_5,zero_12_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_33 : {v : ℝ // smallCoefficient 0 12 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property,zero_12_moment_4.property,zero_12_moment_5.property,zero_12_moment_6.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3,zero_12_moment_4,zero_12_moment_5,zero_12_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_34 : {v : ℝ // smallCoefficient 0 12 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property,zero_12_moment_4.property,zero_12_moment_5.property,zero_12_moment_6.property,zero_12_moment_7.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3,zero_12_moment_4,zero_12_moment_5,zero_12_moment_6,zero_12_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_cell_44 : {v : ℝ // smallCoefficient 0 12 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_12_moment_0.property,zero_12_moment_1.property,zero_12_moment_2.property,zero_12_moment_3.property,zero_12_moment_4.property,zero_12_moment_5.property,zero_12_moment_6.property,zero_12_moment_7.property,zero_12_moment_8.property]
      dsimp only [zero_12_moment_0,zero_12_moment_1,zero_12_moment_2,zero_12_moment_3,zero_12_moment_4,zero_12_moment_5,zero_12_moment_6,zero_12_moment_7,zero_12_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_12_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_12_cell_00.val,zero_12_cell_01.val,zero_12_cell_02.val,zero_12_cell_03.val,zero_12_cell_04.val],
    ![zero_12_cell_01.val,zero_12_cell_11.val,zero_12_cell_12.val,zero_12_cell_13.val,zero_12_cell_14.val],
    ![zero_12_cell_02.val,zero_12_cell_12.val,zero_12_cell_22.val,zero_12_cell_23.val,zero_12_cell_24.val],
    ![zero_12_cell_03.val,zero_12_cell_13.val,zero_12_cell_23.val,zero_12_cell_33.val,zero_12_cell_34.val],
    ![zero_12_cell_04.val,zero_12_cell_14.val,zero_12_cell_24.val,zero_12_cell_34.val,zero_12_cell_44.val]]

private theorem zero_12_matrix_eq : smallCoefficient 0 12=zero_12_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_12_cell_00.property
  · exact zero_12_cell_01.property
  · exact zero_12_cell_02.property
  · exact zero_12_cell_03.property
  · exact zero_12_cell_04.property
  · exact (smallCoefficient_symmetric 0 12 1 0).trans zero_12_cell_01.property
  · exact zero_12_cell_11.property
  · exact zero_12_cell_12.property
  · exact zero_12_cell_13.property
  · exact zero_12_cell_14.property
  · exact (smallCoefficient_symmetric 0 12 2 0).trans zero_12_cell_02.property
  · exact (smallCoefficient_symmetric 0 12 2 1).trans zero_12_cell_12.property
  · exact zero_12_cell_22.property
  · exact zero_12_cell_23.property
  · exact zero_12_cell_24.property
  · exact (smallCoefficient_symmetric 0 12 3 0).trans zero_12_cell_03.property
  · exact (smallCoefficient_symmetric 0 12 3 1).trans zero_12_cell_13.property
  · exact (smallCoefficient_symmetric 0 12 3 2).trans zero_12_cell_23.property
  · exact zero_12_cell_33.property
  · exact zero_12_cell_34.property
  · exact (smallCoefficient_symmetric 0 12 4 0).trans zero_12_cell_04.property
  · exact (smallCoefficient_symmetric 0 12 4 1).trans zero_12_cell_14.property
  · exact (smallCoefficient_symmetric 0 12 4 2).trans zero_12_cell_24.property
  · exact (smallCoefficient_symmetric 0 12 4 3).trans zero_12_cell_34.property
  · exact zero_12_cell_44.property

private theorem zero_12_first_pos : 0 < zero_12_matrix 0 0 := by
  dsimp only [zero_12_matrix,zero_12_cell_00,zero_12_cell_01,zero_12_cell_02,zero_12_cell_03,zero_12_cell_04,zero_12_cell_11,zero_12_cell_12,zero_12_cell_13,zero_12_cell_14,zero_12_cell_22,zero_12_cell_23,zero_12_cell_24,zero_12_cell_33,zero_12_cell_34,zero_12_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_12_delta_pos : 0 < delta zero_12_matrix := by
  dsimp only [zero_12_matrix,zero_12_cell_00,zero_12_cell_01,zero_12_cell_02,zero_12_cell_03,zero_12_cell_04,zero_12_cell_11,zero_12_cell_12,zero_12_cell_13,zero_12_cell_14,zero_12_cell_22,zero_12_cell_23,zero_12_cell_24,zero_12_cell_33,zero_12_cell_34,zero_12_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_12_schur_pos : 0 < schur zero_12_matrix 0 0 := by
  dsimp only [zero_12_matrix,zero_12_cell_00,zero_12_cell_01,zero_12_cell_02,zero_12_cell_03,zero_12_cell_04,zero_12_cell_11,zero_12_cell_12,zero_12_cell_13,zero_12_cell_14,zero_12_cell_22,zero_12_cell_23,zero_12_cell_24,zero_12_cell_33,zero_12_cell_34,zero_12_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_12_minor_pos : 0 < minor zero_12_matrix := by
  dsimp only [zero_12_matrix,zero_12_cell_00,zero_12_cell_01,zero_12_cell_02,zero_12_cell_03,zero_12_cell_04,zero_12_cell_11,zero_12_cell_12,zero_12_cell_13,zero_12_cell_14,zero_12_cell_22,zero_12_cell_23,zero_12_cell_24,zero_12_cell_33,zero_12_cell_34,zero_12_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_12_det_pos : 0 < determinant zero_12_matrix := by
  dsimp only [zero_12_matrix,zero_12_cell_00,zero_12_cell_01,zero_12_cell_02,zero_12_cell_03,zero_12_cell_04,zero_12_cell_11,zero_12_cell_12,zero_12_cell_13,zero_12_cell_14,zero_12_cell_22,zero_12_cell_23,zero_12_cell_24,zero_12_cell_33,zero_12_cell_34,zero_12_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_12_matrix_posDef : zero_12_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_12_first_pos zero_12_delta_pos zero_12_schur_pos
    zero_12_minor_pos zero_12_det_pos
  intro i j
  rw [← zero_12_matrix_eq]
  exact smallCoefficient_symmetric 0 12 i j

private theorem zero_12_posDef : (smallCoefficient 0 12).PosDef := by
  rw [zero_12_matrix_eq]
  exact zero_12_matrix_posDef


private def zero_13_moment_0 : {v : ℝ // momentCoefficient 0 13 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_13_moment_1 : {v : ℝ // momentCoefficient 0 13 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_13_moment_2 : {v : ℝ // momentCoefficient 0 13 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_13_moment_3 : {v : ℝ // momentCoefficient 0 13 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_13_moment_4 : {v : ℝ // momentCoefficient 0 13 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_13_moment_5 : {v : ℝ // momentCoefficient 0 13 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_13_moment_6 : {v : ℝ // momentCoefficient 0 13 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_13_moment_7 : {v : ℝ // momentCoefficient 0 13 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_13_moment_8 : {v : ℝ // momentCoefficient 0 13 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_13_cell_00 : {v : ℝ // smallCoefficient 0 13 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_13_moment_0.property]
      dsimp only [zero_13_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_01 : {v : ℝ // smallCoefficient 0 13 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_13_moment_0.property,zero_13_moment_1.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_02 : {v : ℝ // smallCoefficient 0 13 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_03 : {v : ℝ // smallCoefficient 0 13 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_04 : {v : ℝ // smallCoefficient 0 13 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property,zero_13_moment_4.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3,zero_13_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_11 : {v : ℝ // smallCoefficient 0 13 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_12 : {v : ℝ // smallCoefficient 0 13 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_13 : {v : ℝ // smallCoefficient 0 13 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property,zero_13_moment_4.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3,zero_13_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_14 : {v : ℝ // smallCoefficient 0 13 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property,zero_13_moment_4.property,zero_13_moment_5.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3,zero_13_moment_4,zero_13_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_22 : {v : ℝ // smallCoefficient 0 13 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property,zero_13_moment_4.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3,zero_13_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_23 : {v : ℝ // smallCoefficient 0 13 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property,zero_13_moment_4.property,zero_13_moment_5.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3,zero_13_moment_4,zero_13_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_24 : {v : ℝ // smallCoefficient 0 13 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property,zero_13_moment_4.property,zero_13_moment_5.property,zero_13_moment_6.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3,zero_13_moment_4,zero_13_moment_5,zero_13_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_33 : {v : ℝ // smallCoefficient 0 13 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property,zero_13_moment_4.property,zero_13_moment_5.property,zero_13_moment_6.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3,zero_13_moment_4,zero_13_moment_5,zero_13_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_34 : {v : ℝ // smallCoefficient 0 13 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property,zero_13_moment_4.property,zero_13_moment_5.property,zero_13_moment_6.property,zero_13_moment_7.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3,zero_13_moment_4,zero_13_moment_5,zero_13_moment_6,zero_13_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_cell_44 : {v : ℝ // smallCoefficient 0 13 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_13_moment_0.property,zero_13_moment_1.property,zero_13_moment_2.property,zero_13_moment_3.property,zero_13_moment_4.property,zero_13_moment_5.property,zero_13_moment_6.property,zero_13_moment_7.property,zero_13_moment_8.property]
      dsimp only [zero_13_moment_0,zero_13_moment_1,zero_13_moment_2,zero_13_moment_3,zero_13_moment_4,zero_13_moment_5,zero_13_moment_6,zero_13_moment_7,zero_13_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_13_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_13_cell_00.val,zero_13_cell_01.val,zero_13_cell_02.val,zero_13_cell_03.val,zero_13_cell_04.val],
    ![zero_13_cell_01.val,zero_13_cell_11.val,zero_13_cell_12.val,zero_13_cell_13.val,zero_13_cell_14.val],
    ![zero_13_cell_02.val,zero_13_cell_12.val,zero_13_cell_22.val,zero_13_cell_23.val,zero_13_cell_24.val],
    ![zero_13_cell_03.val,zero_13_cell_13.val,zero_13_cell_23.val,zero_13_cell_33.val,zero_13_cell_34.val],
    ![zero_13_cell_04.val,zero_13_cell_14.val,zero_13_cell_24.val,zero_13_cell_34.val,zero_13_cell_44.val]]

private theorem zero_13_matrix_eq : smallCoefficient 0 13=zero_13_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_13_cell_00.property
  · exact zero_13_cell_01.property
  · exact zero_13_cell_02.property
  · exact zero_13_cell_03.property
  · exact zero_13_cell_04.property
  · exact (smallCoefficient_symmetric 0 13 1 0).trans zero_13_cell_01.property
  · exact zero_13_cell_11.property
  · exact zero_13_cell_12.property
  · exact zero_13_cell_13.property
  · exact zero_13_cell_14.property
  · exact (smallCoefficient_symmetric 0 13 2 0).trans zero_13_cell_02.property
  · exact (smallCoefficient_symmetric 0 13 2 1).trans zero_13_cell_12.property
  · exact zero_13_cell_22.property
  · exact zero_13_cell_23.property
  · exact zero_13_cell_24.property
  · exact (smallCoefficient_symmetric 0 13 3 0).trans zero_13_cell_03.property
  · exact (smallCoefficient_symmetric 0 13 3 1).trans zero_13_cell_13.property
  · exact (smallCoefficient_symmetric 0 13 3 2).trans zero_13_cell_23.property
  · exact zero_13_cell_33.property
  · exact zero_13_cell_34.property
  · exact (smallCoefficient_symmetric 0 13 4 0).trans zero_13_cell_04.property
  · exact (smallCoefficient_symmetric 0 13 4 1).trans zero_13_cell_14.property
  · exact (smallCoefficient_symmetric 0 13 4 2).trans zero_13_cell_24.property
  · exact (smallCoefficient_symmetric 0 13 4 3).trans zero_13_cell_34.property
  · exact zero_13_cell_44.property

private theorem zero_13_first_pos : 0 < zero_13_matrix 0 0 := by
  dsimp only [zero_13_matrix,zero_13_cell_00,zero_13_cell_01,zero_13_cell_02,zero_13_cell_03,zero_13_cell_04,zero_13_cell_11,zero_13_cell_12,zero_13_cell_13,zero_13_cell_14,zero_13_cell_22,zero_13_cell_23,zero_13_cell_24,zero_13_cell_33,zero_13_cell_34,zero_13_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_13_delta_pos : 0 < delta zero_13_matrix := by
  dsimp only [zero_13_matrix,zero_13_cell_00,zero_13_cell_01,zero_13_cell_02,zero_13_cell_03,zero_13_cell_04,zero_13_cell_11,zero_13_cell_12,zero_13_cell_13,zero_13_cell_14,zero_13_cell_22,zero_13_cell_23,zero_13_cell_24,zero_13_cell_33,zero_13_cell_34,zero_13_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_13_schur_pos : 0 < schur zero_13_matrix 0 0 := by
  dsimp only [zero_13_matrix,zero_13_cell_00,zero_13_cell_01,zero_13_cell_02,zero_13_cell_03,zero_13_cell_04,zero_13_cell_11,zero_13_cell_12,zero_13_cell_13,zero_13_cell_14,zero_13_cell_22,zero_13_cell_23,zero_13_cell_24,zero_13_cell_33,zero_13_cell_34,zero_13_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_13_minor_pos : 0 < minor zero_13_matrix := by
  dsimp only [zero_13_matrix,zero_13_cell_00,zero_13_cell_01,zero_13_cell_02,zero_13_cell_03,zero_13_cell_04,zero_13_cell_11,zero_13_cell_12,zero_13_cell_13,zero_13_cell_14,zero_13_cell_22,zero_13_cell_23,zero_13_cell_24,zero_13_cell_33,zero_13_cell_34,zero_13_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_13_det_pos : 0 < determinant zero_13_matrix := by
  dsimp only [zero_13_matrix,zero_13_cell_00,zero_13_cell_01,zero_13_cell_02,zero_13_cell_03,zero_13_cell_04,zero_13_cell_11,zero_13_cell_12,zero_13_cell_13,zero_13_cell_14,zero_13_cell_22,zero_13_cell_23,zero_13_cell_24,zero_13_cell_33,zero_13_cell_34,zero_13_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_13_matrix_posDef : zero_13_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_13_first_pos zero_13_delta_pos zero_13_schur_pos
    zero_13_minor_pos zero_13_det_pos
  intro i j
  rw [← zero_13_matrix_eq]
  exact smallCoefficient_symmetric 0 13 i j

private theorem zero_13_posDef : (smallCoefficient 0 13).PosDef := by
  rw [zero_13_matrix_eq]
  exact zero_13_matrix_posDef


private def zero_14_moment_0 : {v : ℝ // momentCoefficient 0 14 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_14_moment_1 : {v : ℝ // momentCoefficient 0 14 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_14_moment_2 : {v : ℝ // momentCoefficient 0 14 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_14_moment_3 : {v : ℝ // momentCoefficient 0 14 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_14_moment_4 : {v : ℝ // momentCoefficient 0 14 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_14_moment_5 : {v : ℝ // momentCoefficient 0 14 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_14_moment_6 : {v : ℝ // momentCoefficient 0 14 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_14_moment_7 : {v : ℝ // momentCoefficient 0 14 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_14_moment_8 : {v : ℝ // momentCoefficient 0 14 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_14_cell_00 : {v : ℝ // smallCoefficient 0 14 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_14_moment_0.property]
      dsimp only [zero_14_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_01 : {v : ℝ // smallCoefficient 0 14 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_14_moment_0.property,zero_14_moment_1.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_02 : {v : ℝ // smallCoefficient 0 14 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_03 : {v : ℝ // smallCoefficient 0 14 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_04 : {v : ℝ // smallCoefficient 0 14 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property,zero_14_moment_4.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3,zero_14_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_11 : {v : ℝ // smallCoefficient 0 14 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_12 : {v : ℝ // smallCoefficient 0 14 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_13 : {v : ℝ // smallCoefficient 0 14 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property,zero_14_moment_4.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3,zero_14_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_14 : {v : ℝ // smallCoefficient 0 14 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property,zero_14_moment_4.property,zero_14_moment_5.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3,zero_14_moment_4,zero_14_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_22 : {v : ℝ // smallCoefficient 0 14 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property,zero_14_moment_4.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3,zero_14_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_23 : {v : ℝ // smallCoefficient 0 14 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property,zero_14_moment_4.property,zero_14_moment_5.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3,zero_14_moment_4,zero_14_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_24 : {v : ℝ // smallCoefficient 0 14 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property,zero_14_moment_4.property,zero_14_moment_5.property,zero_14_moment_6.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3,zero_14_moment_4,zero_14_moment_5,zero_14_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_33 : {v : ℝ // smallCoefficient 0 14 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property,zero_14_moment_4.property,zero_14_moment_5.property,zero_14_moment_6.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3,zero_14_moment_4,zero_14_moment_5,zero_14_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_34 : {v : ℝ // smallCoefficient 0 14 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property,zero_14_moment_4.property,zero_14_moment_5.property,zero_14_moment_6.property,zero_14_moment_7.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3,zero_14_moment_4,zero_14_moment_5,zero_14_moment_6,zero_14_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_cell_44 : {v : ℝ // smallCoefficient 0 14 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_14_moment_0.property,zero_14_moment_1.property,zero_14_moment_2.property,zero_14_moment_3.property,zero_14_moment_4.property,zero_14_moment_5.property,zero_14_moment_6.property,zero_14_moment_7.property,zero_14_moment_8.property]
      dsimp only [zero_14_moment_0,zero_14_moment_1,zero_14_moment_2,zero_14_moment_3,zero_14_moment_4,zero_14_moment_5,zero_14_moment_6,zero_14_moment_7,zero_14_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_14_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_14_cell_00.val,zero_14_cell_01.val,zero_14_cell_02.val,zero_14_cell_03.val,zero_14_cell_04.val],
    ![zero_14_cell_01.val,zero_14_cell_11.val,zero_14_cell_12.val,zero_14_cell_13.val,zero_14_cell_14.val],
    ![zero_14_cell_02.val,zero_14_cell_12.val,zero_14_cell_22.val,zero_14_cell_23.val,zero_14_cell_24.val],
    ![zero_14_cell_03.val,zero_14_cell_13.val,zero_14_cell_23.val,zero_14_cell_33.val,zero_14_cell_34.val],
    ![zero_14_cell_04.val,zero_14_cell_14.val,zero_14_cell_24.val,zero_14_cell_34.val,zero_14_cell_44.val]]

private theorem zero_14_matrix_eq : smallCoefficient 0 14=zero_14_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_14_cell_00.property
  · exact zero_14_cell_01.property
  · exact zero_14_cell_02.property
  · exact zero_14_cell_03.property
  · exact zero_14_cell_04.property
  · exact (smallCoefficient_symmetric 0 14 1 0).trans zero_14_cell_01.property
  · exact zero_14_cell_11.property
  · exact zero_14_cell_12.property
  · exact zero_14_cell_13.property
  · exact zero_14_cell_14.property
  · exact (smallCoefficient_symmetric 0 14 2 0).trans zero_14_cell_02.property
  · exact (smallCoefficient_symmetric 0 14 2 1).trans zero_14_cell_12.property
  · exact zero_14_cell_22.property
  · exact zero_14_cell_23.property
  · exact zero_14_cell_24.property
  · exact (smallCoefficient_symmetric 0 14 3 0).trans zero_14_cell_03.property
  · exact (smallCoefficient_symmetric 0 14 3 1).trans zero_14_cell_13.property
  · exact (smallCoefficient_symmetric 0 14 3 2).trans zero_14_cell_23.property
  · exact zero_14_cell_33.property
  · exact zero_14_cell_34.property
  · exact (smallCoefficient_symmetric 0 14 4 0).trans zero_14_cell_04.property
  · exact (smallCoefficient_symmetric 0 14 4 1).trans zero_14_cell_14.property
  · exact (smallCoefficient_symmetric 0 14 4 2).trans zero_14_cell_24.property
  · exact (smallCoefficient_symmetric 0 14 4 3).trans zero_14_cell_34.property
  · exact zero_14_cell_44.property

private theorem zero_14_first_pos : 0 < zero_14_matrix 0 0 := by
  dsimp only [zero_14_matrix,zero_14_cell_00,zero_14_cell_01,zero_14_cell_02,zero_14_cell_03,zero_14_cell_04,zero_14_cell_11,zero_14_cell_12,zero_14_cell_13,zero_14_cell_14,zero_14_cell_22,zero_14_cell_23,zero_14_cell_24,zero_14_cell_33,zero_14_cell_34,zero_14_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_14_delta_pos : 0 < delta zero_14_matrix := by
  dsimp only [zero_14_matrix,zero_14_cell_00,zero_14_cell_01,zero_14_cell_02,zero_14_cell_03,zero_14_cell_04,zero_14_cell_11,zero_14_cell_12,zero_14_cell_13,zero_14_cell_14,zero_14_cell_22,zero_14_cell_23,zero_14_cell_24,zero_14_cell_33,zero_14_cell_34,zero_14_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_14_schur_pos : 0 < schur zero_14_matrix 0 0 := by
  dsimp only [zero_14_matrix,zero_14_cell_00,zero_14_cell_01,zero_14_cell_02,zero_14_cell_03,zero_14_cell_04,zero_14_cell_11,zero_14_cell_12,zero_14_cell_13,zero_14_cell_14,zero_14_cell_22,zero_14_cell_23,zero_14_cell_24,zero_14_cell_33,zero_14_cell_34,zero_14_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_14_minor_pos : 0 < minor zero_14_matrix := by
  dsimp only [zero_14_matrix,zero_14_cell_00,zero_14_cell_01,zero_14_cell_02,zero_14_cell_03,zero_14_cell_04,zero_14_cell_11,zero_14_cell_12,zero_14_cell_13,zero_14_cell_14,zero_14_cell_22,zero_14_cell_23,zero_14_cell_24,zero_14_cell_33,zero_14_cell_34,zero_14_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_14_det_pos : 0 < determinant zero_14_matrix := by
  dsimp only [zero_14_matrix,zero_14_cell_00,zero_14_cell_01,zero_14_cell_02,zero_14_cell_03,zero_14_cell_04,zero_14_cell_11,zero_14_cell_12,zero_14_cell_13,zero_14_cell_14,zero_14_cell_22,zero_14_cell_23,zero_14_cell_24,zero_14_cell_33,zero_14_cell_34,zero_14_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_14_matrix_posDef : zero_14_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_14_first_pos zero_14_delta_pos zero_14_schur_pos
    zero_14_minor_pos zero_14_det_pos
  intro i j
  rw [← zero_14_matrix_eq]
  exact smallCoefficient_symmetric 0 14 i j

private theorem zero_14_posDef : (smallCoefficient 0 14).PosDef := by
  rw [zero_14_matrix_eq]
  exact zero_14_matrix_posDef


private def zero_15_moment_0 : {v : ℝ // momentCoefficient 0 15 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_15_moment_1 : {v : ℝ // momentCoefficient 0 15 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_15_moment_2 : {v : ℝ // momentCoefficient 0 15 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_15_moment_3 : {v : ℝ // momentCoefficient 0 15 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_15_moment_4 : {v : ℝ // momentCoefficient 0 15 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_15_moment_5 : {v : ℝ // momentCoefficient 0 15 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_15_moment_6 : {v : ℝ // momentCoefficient 0 15 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_15_moment_7 : {v : ℝ // momentCoefficient 0 15 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_15_moment_8 : {v : ℝ // momentCoefficient 0 15 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_15_cell_00 : {v : ℝ // smallCoefficient 0 15 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_15_moment_0.property]
      dsimp only [zero_15_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_01 : {v : ℝ // smallCoefficient 0 15 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_15_moment_0.property,zero_15_moment_1.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_02 : {v : ℝ // smallCoefficient 0 15 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_03 : {v : ℝ // smallCoefficient 0 15 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_04 : {v : ℝ // smallCoefficient 0 15 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property,zero_15_moment_4.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3,zero_15_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_11 : {v : ℝ // smallCoefficient 0 15 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_12 : {v : ℝ // smallCoefficient 0 15 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_13 : {v : ℝ // smallCoefficient 0 15 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property,zero_15_moment_4.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3,zero_15_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_14 : {v : ℝ // smallCoefficient 0 15 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property,zero_15_moment_4.property,zero_15_moment_5.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3,zero_15_moment_4,zero_15_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_22 : {v : ℝ // smallCoefficient 0 15 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property,zero_15_moment_4.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3,zero_15_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_23 : {v : ℝ // smallCoefficient 0 15 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property,zero_15_moment_4.property,zero_15_moment_5.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3,zero_15_moment_4,zero_15_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_24 : {v : ℝ // smallCoefficient 0 15 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property,zero_15_moment_4.property,zero_15_moment_5.property,zero_15_moment_6.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3,zero_15_moment_4,zero_15_moment_5,zero_15_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_33 : {v : ℝ // smallCoefficient 0 15 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property,zero_15_moment_4.property,zero_15_moment_5.property,zero_15_moment_6.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3,zero_15_moment_4,zero_15_moment_5,zero_15_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_34 : {v : ℝ // smallCoefficient 0 15 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property,zero_15_moment_4.property,zero_15_moment_5.property,zero_15_moment_6.property,zero_15_moment_7.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3,zero_15_moment_4,zero_15_moment_5,zero_15_moment_6,zero_15_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_cell_44 : {v : ℝ // smallCoefficient 0 15 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_15_moment_0.property,zero_15_moment_1.property,zero_15_moment_2.property,zero_15_moment_3.property,zero_15_moment_4.property,zero_15_moment_5.property,zero_15_moment_6.property,zero_15_moment_7.property,zero_15_moment_8.property]
      dsimp only [zero_15_moment_0,zero_15_moment_1,zero_15_moment_2,zero_15_moment_3,zero_15_moment_4,zero_15_moment_5,zero_15_moment_6,zero_15_moment_7,zero_15_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_15_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_15_cell_00.val,zero_15_cell_01.val,zero_15_cell_02.val,zero_15_cell_03.val,zero_15_cell_04.val],
    ![zero_15_cell_01.val,zero_15_cell_11.val,zero_15_cell_12.val,zero_15_cell_13.val,zero_15_cell_14.val],
    ![zero_15_cell_02.val,zero_15_cell_12.val,zero_15_cell_22.val,zero_15_cell_23.val,zero_15_cell_24.val],
    ![zero_15_cell_03.val,zero_15_cell_13.val,zero_15_cell_23.val,zero_15_cell_33.val,zero_15_cell_34.val],
    ![zero_15_cell_04.val,zero_15_cell_14.val,zero_15_cell_24.val,zero_15_cell_34.val,zero_15_cell_44.val]]

private theorem zero_15_matrix_eq : smallCoefficient 0 15=zero_15_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_15_cell_00.property
  · exact zero_15_cell_01.property
  · exact zero_15_cell_02.property
  · exact zero_15_cell_03.property
  · exact zero_15_cell_04.property
  · exact (smallCoefficient_symmetric 0 15 1 0).trans zero_15_cell_01.property
  · exact zero_15_cell_11.property
  · exact zero_15_cell_12.property
  · exact zero_15_cell_13.property
  · exact zero_15_cell_14.property
  · exact (smallCoefficient_symmetric 0 15 2 0).trans zero_15_cell_02.property
  · exact (smallCoefficient_symmetric 0 15 2 1).trans zero_15_cell_12.property
  · exact zero_15_cell_22.property
  · exact zero_15_cell_23.property
  · exact zero_15_cell_24.property
  · exact (smallCoefficient_symmetric 0 15 3 0).trans zero_15_cell_03.property
  · exact (smallCoefficient_symmetric 0 15 3 1).trans zero_15_cell_13.property
  · exact (smallCoefficient_symmetric 0 15 3 2).trans zero_15_cell_23.property
  · exact zero_15_cell_33.property
  · exact zero_15_cell_34.property
  · exact (smallCoefficient_symmetric 0 15 4 0).trans zero_15_cell_04.property
  · exact (smallCoefficient_symmetric 0 15 4 1).trans zero_15_cell_14.property
  · exact (smallCoefficient_symmetric 0 15 4 2).trans zero_15_cell_24.property
  · exact (smallCoefficient_symmetric 0 15 4 3).trans zero_15_cell_34.property
  · exact zero_15_cell_44.property

private theorem zero_15_first_pos : 0 < zero_15_matrix 0 0 := by
  dsimp only [zero_15_matrix,zero_15_cell_00,zero_15_cell_01,zero_15_cell_02,zero_15_cell_03,zero_15_cell_04,zero_15_cell_11,zero_15_cell_12,zero_15_cell_13,zero_15_cell_14,zero_15_cell_22,zero_15_cell_23,zero_15_cell_24,zero_15_cell_33,zero_15_cell_34,zero_15_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_15_delta_pos : 0 < delta zero_15_matrix := by
  dsimp only [zero_15_matrix,zero_15_cell_00,zero_15_cell_01,zero_15_cell_02,zero_15_cell_03,zero_15_cell_04,zero_15_cell_11,zero_15_cell_12,zero_15_cell_13,zero_15_cell_14,zero_15_cell_22,zero_15_cell_23,zero_15_cell_24,zero_15_cell_33,zero_15_cell_34,zero_15_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_15_schur_pos : 0 < schur zero_15_matrix 0 0 := by
  dsimp only [zero_15_matrix,zero_15_cell_00,zero_15_cell_01,zero_15_cell_02,zero_15_cell_03,zero_15_cell_04,zero_15_cell_11,zero_15_cell_12,zero_15_cell_13,zero_15_cell_14,zero_15_cell_22,zero_15_cell_23,zero_15_cell_24,zero_15_cell_33,zero_15_cell_34,zero_15_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_15_minor_pos : 0 < minor zero_15_matrix := by
  dsimp only [zero_15_matrix,zero_15_cell_00,zero_15_cell_01,zero_15_cell_02,zero_15_cell_03,zero_15_cell_04,zero_15_cell_11,zero_15_cell_12,zero_15_cell_13,zero_15_cell_14,zero_15_cell_22,zero_15_cell_23,zero_15_cell_24,zero_15_cell_33,zero_15_cell_34,zero_15_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_15_det_pos : 0 < determinant zero_15_matrix := by
  dsimp only [zero_15_matrix,zero_15_cell_00,zero_15_cell_01,zero_15_cell_02,zero_15_cell_03,zero_15_cell_04,zero_15_cell_11,zero_15_cell_12,zero_15_cell_13,zero_15_cell_14,zero_15_cell_22,zero_15_cell_23,zero_15_cell_24,zero_15_cell_33,zero_15_cell_34,zero_15_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_15_matrix_posDef : zero_15_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_15_first_pos zero_15_delta_pos zero_15_schur_pos
    zero_15_minor_pos zero_15_det_pos
  intro i j
  rw [← zero_15_matrix_eq]
  exact smallCoefficient_symmetric 0 15 i j

private theorem zero_15_posDef : (smallCoefficient 0 15).PosDef := by
  rw [zero_15_matrix_eq]
  exact zero_15_matrix_posDef


private def zero_16_moment_0 : {v : ℝ // momentCoefficient 0 16 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_16_moment_1 : {v : ℝ // momentCoefficient 0 16 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_16_moment_2 : {v : ℝ // momentCoefficient 0 16 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_16_moment_3 : {v : ℝ // momentCoefficient 0 16 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_16_moment_4 : {v : ℝ // momentCoefficient 0 16 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_16_moment_5 : {v : ℝ // momentCoefficient 0 16 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_16_moment_6 : {v : ℝ // momentCoefficient 0 16 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_16_moment_7 : {v : ℝ // momentCoefficient 0 16 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_16_moment_8 : {v : ℝ // momentCoefficient 0 16 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_16_cell_00 : {v : ℝ // smallCoefficient 0 16 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_16_moment_0.property]
      dsimp only [zero_16_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_01 : {v : ℝ // smallCoefficient 0 16 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_16_moment_0.property,zero_16_moment_1.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_02 : {v : ℝ // smallCoefficient 0 16 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_03 : {v : ℝ // smallCoefficient 0 16 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_04 : {v : ℝ // smallCoefficient 0 16 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property,zero_16_moment_4.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3,zero_16_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_11 : {v : ℝ // smallCoefficient 0 16 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_12 : {v : ℝ // smallCoefficient 0 16 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_13 : {v : ℝ // smallCoefficient 0 16 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property,zero_16_moment_4.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3,zero_16_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_14 : {v : ℝ // smallCoefficient 0 16 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property,zero_16_moment_4.property,zero_16_moment_5.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3,zero_16_moment_4,zero_16_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_22 : {v : ℝ // smallCoefficient 0 16 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property,zero_16_moment_4.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3,zero_16_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_23 : {v : ℝ // smallCoefficient 0 16 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property,zero_16_moment_4.property,zero_16_moment_5.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3,zero_16_moment_4,zero_16_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_24 : {v : ℝ // smallCoefficient 0 16 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property,zero_16_moment_4.property,zero_16_moment_5.property,zero_16_moment_6.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3,zero_16_moment_4,zero_16_moment_5,zero_16_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_33 : {v : ℝ // smallCoefficient 0 16 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property,zero_16_moment_4.property,zero_16_moment_5.property,zero_16_moment_6.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3,zero_16_moment_4,zero_16_moment_5,zero_16_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_34 : {v : ℝ // smallCoefficient 0 16 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property,zero_16_moment_4.property,zero_16_moment_5.property,zero_16_moment_6.property,zero_16_moment_7.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3,zero_16_moment_4,zero_16_moment_5,zero_16_moment_6,zero_16_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_cell_44 : {v : ℝ // smallCoefficient 0 16 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_16_moment_0.property,zero_16_moment_1.property,zero_16_moment_2.property,zero_16_moment_3.property,zero_16_moment_4.property,zero_16_moment_5.property,zero_16_moment_6.property,zero_16_moment_7.property,zero_16_moment_8.property]
      dsimp only [zero_16_moment_0,zero_16_moment_1,zero_16_moment_2,zero_16_moment_3,zero_16_moment_4,zero_16_moment_5,zero_16_moment_6,zero_16_moment_7,zero_16_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_16_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_16_cell_00.val,zero_16_cell_01.val,zero_16_cell_02.val,zero_16_cell_03.val,zero_16_cell_04.val],
    ![zero_16_cell_01.val,zero_16_cell_11.val,zero_16_cell_12.val,zero_16_cell_13.val,zero_16_cell_14.val],
    ![zero_16_cell_02.val,zero_16_cell_12.val,zero_16_cell_22.val,zero_16_cell_23.val,zero_16_cell_24.val],
    ![zero_16_cell_03.val,zero_16_cell_13.val,zero_16_cell_23.val,zero_16_cell_33.val,zero_16_cell_34.val],
    ![zero_16_cell_04.val,zero_16_cell_14.val,zero_16_cell_24.val,zero_16_cell_34.val,zero_16_cell_44.val]]

private theorem zero_16_matrix_eq : smallCoefficient 0 16=zero_16_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_16_cell_00.property
  · exact zero_16_cell_01.property
  · exact zero_16_cell_02.property
  · exact zero_16_cell_03.property
  · exact zero_16_cell_04.property
  · exact (smallCoefficient_symmetric 0 16 1 0).trans zero_16_cell_01.property
  · exact zero_16_cell_11.property
  · exact zero_16_cell_12.property
  · exact zero_16_cell_13.property
  · exact zero_16_cell_14.property
  · exact (smallCoefficient_symmetric 0 16 2 0).trans zero_16_cell_02.property
  · exact (smallCoefficient_symmetric 0 16 2 1).trans zero_16_cell_12.property
  · exact zero_16_cell_22.property
  · exact zero_16_cell_23.property
  · exact zero_16_cell_24.property
  · exact (smallCoefficient_symmetric 0 16 3 0).trans zero_16_cell_03.property
  · exact (smallCoefficient_symmetric 0 16 3 1).trans zero_16_cell_13.property
  · exact (smallCoefficient_symmetric 0 16 3 2).trans zero_16_cell_23.property
  · exact zero_16_cell_33.property
  · exact zero_16_cell_34.property
  · exact (smallCoefficient_symmetric 0 16 4 0).trans zero_16_cell_04.property
  · exact (smallCoefficient_symmetric 0 16 4 1).trans zero_16_cell_14.property
  · exact (smallCoefficient_symmetric 0 16 4 2).trans zero_16_cell_24.property
  · exact (smallCoefficient_symmetric 0 16 4 3).trans zero_16_cell_34.property
  · exact zero_16_cell_44.property

private theorem zero_16_first_pos : 0 < zero_16_matrix 0 0 := by
  dsimp only [zero_16_matrix,zero_16_cell_00,zero_16_cell_01,zero_16_cell_02,zero_16_cell_03,zero_16_cell_04,zero_16_cell_11,zero_16_cell_12,zero_16_cell_13,zero_16_cell_14,zero_16_cell_22,zero_16_cell_23,zero_16_cell_24,zero_16_cell_33,zero_16_cell_34,zero_16_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_16_delta_pos : 0 < delta zero_16_matrix := by
  dsimp only [zero_16_matrix,zero_16_cell_00,zero_16_cell_01,zero_16_cell_02,zero_16_cell_03,zero_16_cell_04,zero_16_cell_11,zero_16_cell_12,zero_16_cell_13,zero_16_cell_14,zero_16_cell_22,zero_16_cell_23,zero_16_cell_24,zero_16_cell_33,zero_16_cell_34,zero_16_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_16_schur_pos : 0 < schur zero_16_matrix 0 0 := by
  dsimp only [zero_16_matrix,zero_16_cell_00,zero_16_cell_01,zero_16_cell_02,zero_16_cell_03,zero_16_cell_04,zero_16_cell_11,zero_16_cell_12,zero_16_cell_13,zero_16_cell_14,zero_16_cell_22,zero_16_cell_23,zero_16_cell_24,zero_16_cell_33,zero_16_cell_34,zero_16_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_16_minor_pos : 0 < minor zero_16_matrix := by
  dsimp only [zero_16_matrix,zero_16_cell_00,zero_16_cell_01,zero_16_cell_02,zero_16_cell_03,zero_16_cell_04,zero_16_cell_11,zero_16_cell_12,zero_16_cell_13,zero_16_cell_14,zero_16_cell_22,zero_16_cell_23,zero_16_cell_24,zero_16_cell_33,zero_16_cell_34,zero_16_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_16_det_pos : 0 < determinant zero_16_matrix := by
  dsimp only [zero_16_matrix,zero_16_cell_00,zero_16_cell_01,zero_16_cell_02,zero_16_cell_03,zero_16_cell_04,zero_16_cell_11,zero_16_cell_12,zero_16_cell_13,zero_16_cell_14,zero_16_cell_22,zero_16_cell_23,zero_16_cell_24,zero_16_cell_33,zero_16_cell_34,zero_16_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_16_matrix_posDef : zero_16_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_16_first_pos zero_16_delta_pos zero_16_schur_pos
    zero_16_minor_pos zero_16_det_pos
  intro i j
  rw [← zero_16_matrix_eq]
  exact smallCoefficient_symmetric 0 16 i j

private theorem zero_16_posDef : (smallCoefficient 0 16).PosDef := by
  rw [zero_16_matrix_eq]
  exact zero_16_matrix_posDef


private def zero_17_moment_0 : {v : ℝ // momentCoefficient 0 17 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_17_moment_1 : {v : ℝ // momentCoefficient 0 17 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_17_moment_2 : {v : ℝ // momentCoefficient 0 17 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_17_moment_3 : {v : ℝ // momentCoefficient 0 17 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_17_moment_4 : {v : ℝ // momentCoefficient 0 17 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_17_moment_5 : {v : ℝ // momentCoefficient 0 17 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_17_moment_6 : {v : ℝ // momentCoefficient 0 17 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_17_moment_7 : {v : ℝ // momentCoefficient 0 17 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_17_moment_8 : {v : ℝ // momentCoefficient 0 17 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_17_cell_00 : {v : ℝ // smallCoefficient 0 17 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_17_moment_0.property]
      dsimp only [zero_17_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_01 : {v : ℝ // smallCoefficient 0 17 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_17_moment_0.property,zero_17_moment_1.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_02 : {v : ℝ // smallCoefficient 0 17 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_03 : {v : ℝ // smallCoefficient 0 17 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_04 : {v : ℝ // smallCoefficient 0 17 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property,zero_17_moment_4.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3,zero_17_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_11 : {v : ℝ // smallCoefficient 0 17 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_12 : {v : ℝ // smallCoefficient 0 17 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_13 : {v : ℝ // smallCoefficient 0 17 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property,zero_17_moment_4.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3,zero_17_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_14 : {v : ℝ // smallCoefficient 0 17 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property,zero_17_moment_4.property,zero_17_moment_5.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3,zero_17_moment_4,zero_17_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_22 : {v : ℝ // smallCoefficient 0 17 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property,zero_17_moment_4.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3,zero_17_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_23 : {v : ℝ // smallCoefficient 0 17 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property,zero_17_moment_4.property,zero_17_moment_5.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3,zero_17_moment_4,zero_17_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_24 : {v : ℝ // smallCoefficient 0 17 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property,zero_17_moment_4.property,zero_17_moment_5.property,zero_17_moment_6.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3,zero_17_moment_4,zero_17_moment_5,zero_17_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_33 : {v : ℝ // smallCoefficient 0 17 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property,zero_17_moment_4.property,zero_17_moment_5.property,zero_17_moment_6.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3,zero_17_moment_4,zero_17_moment_5,zero_17_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_34 : {v : ℝ // smallCoefficient 0 17 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property,zero_17_moment_4.property,zero_17_moment_5.property,zero_17_moment_6.property,zero_17_moment_7.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3,zero_17_moment_4,zero_17_moment_5,zero_17_moment_6,zero_17_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_cell_44 : {v : ℝ // smallCoefficient 0 17 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_17_moment_0.property,zero_17_moment_1.property,zero_17_moment_2.property,zero_17_moment_3.property,zero_17_moment_4.property,zero_17_moment_5.property,zero_17_moment_6.property,zero_17_moment_7.property,zero_17_moment_8.property]
      dsimp only [zero_17_moment_0,zero_17_moment_1,zero_17_moment_2,zero_17_moment_3,zero_17_moment_4,zero_17_moment_5,zero_17_moment_6,zero_17_moment_7,zero_17_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_17_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_17_cell_00.val,zero_17_cell_01.val,zero_17_cell_02.val,zero_17_cell_03.val,zero_17_cell_04.val],
    ![zero_17_cell_01.val,zero_17_cell_11.val,zero_17_cell_12.val,zero_17_cell_13.val,zero_17_cell_14.val],
    ![zero_17_cell_02.val,zero_17_cell_12.val,zero_17_cell_22.val,zero_17_cell_23.val,zero_17_cell_24.val],
    ![zero_17_cell_03.val,zero_17_cell_13.val,zero_17_cell_23.val,zero_17_cell_33.val,zero_17_cell_34.val],
    ![zero_17_cell_04.val,zero_17_cell_14.val,zero_17_cell_24.val,zero_17_cell_34.val,zero_17_cell_44.val]]

private theorem zero_17_matrix_eq : smallCoefficient 0 17=zero_17_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_17_cell_00.property
  · exact zero_17_cell_01.property
  · exact zero_17_cell_02.property
  · exact zero_17_cell_03.property
  · exact zero_17_cell_04.property
  · exact (smallCoefficient_symmetric 0 17 1 0).trans zero_17_cell_01.property
  · exact zero_17_cell_11.property
  · exact zero_17_cell_12.property
  · exact zero_17_cell_13.property
  · exact zero_17_cell_14.property
  · exact (smallCoefficient_symmetric 0 17 2 0).trans zero_17_cell_02.property
  · exact (smallCoefficient_symmetric 0 17 2 1).trans zero_17_cell_12.property
  · exact zero_17_cell_22.property
  · exact zero_17_cell_23.property
  · exact zero_17_cell_24.property
  · exact (smallCoefficient_symmetric 0 17 3 0).trans zero_17_cell_03.property
  · exact (smallCoefficient_symmetric 0 17 3 1).trans zero_17_cell_13.property
  · exact (smallCoefficient_symmetric 0 17 3 2).trans zero_17_cell_23.property
  · exact zero_17_cell_33.property
  · exact zero_17_cell_34.property
  · exact (smallCoefficient_symmetric 0 17 4 0).trans zero_17_cell_04.property
  · exact (smallCoefficient_symmetric 0 17 4 1).trans zero_17_cell_14.property
  · exact (smallCoefficient_symmetric 0 17 4 2).trans zero_17_cell_24.property
  · exact (smallCoefficient_symmetric 0 17 4 3).trans zero_17_cell_34.property
  · exact zero_17_cell_44.property

private theorem zero_17_first_pos : 0 < zero_17_matrix 0 0 := by
  dsimp only [zero_17_matrix,zero_17_cell_00,zero_17_cell_01,zero_17_cell_02,zero_17_cell_03,zero_17_cell_04,zero_17_cell_11,zero_17_cell_12,zero_17_cell_13,zero_17_cell_14,zero_17_cell_22,zero_17_cell_23,zero_17_cell_24,zero_17_cell_33,zero_17_cell_34,zero_17_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_17_delta_pos : 0 < delta zero_17_matrix := by
  dsimp only [zero_17_matrix,zero_17_cell_00,zero_17_cell_01,zero_17_cell_02,zero_17_cell_03,zero_17_cell_04,zero_17_cell_11,zero_17_cell_12,zero_17_cell_13,zero_17_cell_14,zero_17_cell_22,zero_17_cell_23,zero_17_cell_24,zero_17_cell_33,zero_17_cell_34,zero_17_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_17_schur_pos : 0 < schur zero_17_matrix 0 0 := by
  dsimp only [zero_17_matrix,zero_17_cell_00,zero_17_cell_01,zero_17_cell_02,zero_17_cell_03,zero_17_cell_04,zero_17_cell_11,zero_17_cell_12,zero_17_cell_13,zero_17_cell_14,zero_17_cell_22,zero_17_cell_23,zero_17_cell_24,zero_17_cell_33,zero_17_cell_34,zero_17_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_17_minor_pos : 0 < minor zero_17_matrix := by
  dsimp only [zero_17_matrix,zero_17_cell_00,zero_17_cell_01,zero_17_cell_02,zero_17_cell_03,zero_17_cell_04,zero_17_cell_11,zero_17_cell_12,zero_17_cell_13,zero_17_cell_14,zero_17_cell_22,zero_17_cell_23,zero_17_cell_24,zero_17_cell_33,zero_17_cell_34,zero_17_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_17_det_pos : 0 < determinant zero_17_matrix := by
  dsimp only [zero_17_matrix,zero_17_cell_00,zero_17_cell_01,zero_17_cell_02,zero_17_cell_03,zero_17_cell_04,zero_17_cell_11,zero_17_cell_12,zero_17_cell_13,zero_17_cell_14,zero_17_cell_22,zero_17_cell_23,zero_17_cell_24,zero_17_cell_33,zero_17_cell_34,zero_17_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_17_matrix_posDef : zero_17_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_17_first_pos zero_17_delta_pos zero_17_schur_pos
    zero_17_minor_pos zero_17_det_pos
  intro i j
  rw [← zero_17_matrix_eq]
  exact smallCoefficient_symmetric 0 17 i j

private theorem zero_17_posDef : (smallCoefficient 0 17).PosDef := by
  rw [zero_17_matrix_eq]
  exact zero_17_matrix_posDef


private def zero_18_moment_0 : {v : ℝ // momentCoefficient 0 18 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_18_moment_1 : {v : ℝ // momentCoefficient 0 18 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_18_moment_2 : {v : ℝ // momentCoefficient 0 18 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_18_moment_3 : {v : ℝ // momentCoefficient 0 18 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_18_moment_4 : {v : ℝ // momentCoefficient 0 18 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_18_moment_5 : {v : ℝ // momentCoefficient 0 18 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_18_moment_6 : {v : ℝ // momentCoefficient 0 18 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_18_moment_7 : {v : ℝ // momentCoefficient 0 18 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_18_moment_8 : {v : ℝ // momentCoefficient 0 18 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_18_cell_00 : {v : ℝ // smallCoefficient 0 18 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_18_moment_0.property]
      dsimp only [zero_18_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_01 : {v : ℝ // smallCoefficient 0 18 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_18_moment_0.property,zero_18_moment_1.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_02 : {v : ℝ // smallCoefficient 0 18 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_03 : {v : ℝ // smallCoefficient 0 18 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_04 : {v : ℝ // smallCoefficient 0 18 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property,zero_18_moment_4.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3,zero_18_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_11 : {v : ℝ // smallCoefficient 0 18 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_12 : {v : ℝ // smallCoefficient 0 18 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_13 : {v : ℝ // smallCoefficient 0 18 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property,zero_18_moment_4.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3,zero_18_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_14 : {v : ℝ // smallCoefficient 0 18 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property,zero_18_moment_4.property,zero_18_moment_5.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3,zero_18_moment_4,zero_18_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_22 : {v : ℝ // smallCoefficient 0 18 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property,zero_18_moment_4.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3,zero_18_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_23 : {v : ℝ // smallCoefficient 0 18 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property,zero_18_moment_4.property,zero_18_moment_5.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3,zero_18_moment_4,zero_18_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_24 : {v : ℝ // smallCoefficient 0 18 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property,zero_18_moment_4.property,zero_18_moment_5.property,zero_18_moment_6.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3,zero_18_moment_4,zero_18_moment_5,zero_18_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_33 : {v : ℝ // smallCoefficient 0 18 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property,zero_18_moment_4.property,zero_18_moment_5.property,zero_18_moment_6.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3,zero_18_moment_4,zero_18_moment_5,zero_18_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_34 : {v : ℝ // smallCoefficient 0 18 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property,zero_18_moment_4.property,zero_18_moment_5.property,zero_18_moment_6.property,zero_18_moment_7.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3,zero_18_moment_4,zero_18_moment_5,zero_18_moment_6,zero_18_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_cell_44 : {v : ℝ // smallCoefficient 0 18 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_18_moment_0.property,zero_18_moment_1.property,zero_18_moment_2.property,zero_18_moment_3.property,zero_18_moment_4.property,zero_18_moment_5.property,zero_18_moment_6.property,zero_18_moment_7.property,zero_18_moment_8.property]
      dsimp only [zero_18_moment_0,zero_18_moment_1,zero_18_moment_2,zero_18_moment_3,zero_18_moment_4,zero_18_moment_5,zero_18_moment_6,zero_18_moment_7,zero_18_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_18_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_18_cell_00.val,zero_18_cell_01.val,zero_18_cell_02.val,zero_18_cell_03.val,zero_18_cell_04.val],
    ![zero_18_cell_01.val,zero_18_cell_11.val,zero_18_cell_12.val,zero_18_cell_13.val,zero_18_cell_14.val],
    ![zero_18_cell_02.val,zero_18_cell_12.val,zero_18_cell_22.val,zero_18_cell_23.val,zero_18_cell_24.val],
    ![zero_18_cell_03.val,zero_18_cell_13.val,zero_18_cell_23.val,zero_18_cell_33.val,zero_18_cell_34.val],
    ![zero_18_cell_04.val,zero_18_cell_14.val,zero_18_cell_24.val,zero_18_cell_34.val,zero_18_cell_44.val]]

private theorem zero_18_matrix_eq : smallCoefficient 0 18=zero_18_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_18_cell_00.property
  · exact zero_18_cell_01.property
  · exact zero_18_cell_02.property
  · exact zero_18_cell_03.property
  · exact zero_18_cell_04.property
  · exact (smallCoefficient_symmetric 0 18 1 0).trans zero_18_cell_01.property
  · exact zero_18_cell_11.property
  · exact zero_18_cell_12.property
  · exact zero_18_cell_13.property
  · exact zero_18_cell_14.property
  · exact (smallCoefficient_symmetric 0 18 2 0).trans zero_18_cell_02.property
  · exact (smallCoefficient_symmetric 0 18 2 1).trans zero_18_cell_12.property
  · exact zero_18_cell_22.property
  · exact zero_18_cell_23.property
  · exact zero_18_cell_24.property
  · exact (smallCoefficient_symmetric 0 18 3 0).trans zero_18_cell_03.property
  · exact (smallCoefficient_symmetric 0 18 3 1).trans zero_18_cell_13.property
  · exact (smallCoefficient_symmetric 0 18 3 2).trans zero_18_cell_23.property
  · exact zero_18_cell_33.property
  · exact zero_18_cell_34.property
  · exact (smallCoefficient_symmetric 0 18 4 0).trans zero_18_cell_04.property
  · exact (smallCoefficient_symmetric 0 18 4 1).trans zero_18_cell_14.property
  · exact (smallCoefficient_symmetric 0 18 4 2).trans zero_18_cell_24.property
  · exact (smallCoefficient_symmetric 0 18 4 3).trans zero_18_cell_34.property
  · exact zero_18_cell_44.property

private theorem zero_18_first_pos : 0 < zero_18_matrix 0 0 := by
  dsimp only [zero_18_matrix,zero_18_cell_00,zero_18_cell_01,zero_18_cell_02,zero_18_cell_03,zero_18_cell_04,zero_18_cell_11,zero_18_cell_12,zero_18_cell_13,zero_18_cell_14,zero_18_cell_22,zero_18_cell_23,zero_18_cell_24,zero_18_cell_33,zero_18_cell_34,zero_18_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_18_delta_pos : 0 < delta zero_18_matrix := by
  dsimp only [zero_18_matrix,zero_18_cell_00,zero_18_cell_01,zero_18_cell_02,zero_18_cell_03,zero_18_cell_04,zero_18_cell_11,zero_18_cell_12,zero_18_cell_13,zero_18_cell_14,zero_18_cell_22,zero_18_cell_23,zero_18_cell_24,zero_18_cell_33,zero_18_cell_34,zero_18_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_18_schur_pos : 0 < schur zero_18_matrix 0 0 := by
  dsimp only [zero_18_matrix,zero_18_cell_00,zero_18_cell_01,zero_18_cell_02,zero_18_cell_03,zero_18_cell_04,zero_18_cell_11,zero_18_cell_12,zero_18_cell_13,zero_18_cell_14,zero_18_cell_22,zero_18_cell_23,zero_18_cell_24,zero_18_cell_33,zero_18_cell_34,zero_18_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_18_minor_pos : 0 < minor zero_18_matrix := by
  dsimp only [zero_18_matrix,zero_18_cell_00,zero_18_cell_01,zero_18_cell_02,zero_18_cell_03,zero_18_cell_04,zero_18_cell_11,zero_18_cell_12,zero_18_cell_13,zero_18_cell_14,zero_18_cell_22,zero_18_cell_23,zero_18_cell_24,zero_18_cell_33,zero_18_cell_34,zero_18_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_18_det_pos : 0 < determinant zero_18_matrix := by
  dsimp only [zero_18_matrix,zero_18_cell_00,zero_18_cell_01,zero_18_cell_02,zero_18_cell_03,zero_18_cell_04,zero_18_cell_11,zero_18_cell_12,zero_18_cell_13,zero_18_cell_14,zero_18_cell_22,zero_18_cell_23,zero_18_cell_24,zero_18_cell_33,zero_18_cell_34,zero_18_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_18_matrix_posDef : zero_18_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_18_first_pos zero_18_delta_pos zero_18_schur_pos
    zero_18_minor_pos zero_18_det_pos
  intro i j
  rw [← zero_18_matrix_eq]
  exact smallCoefficient_symmetric 0 18 i j

private theorem zero_18_posDef : (smallCoefficient 0 18).PosDef := by
  rw [zero_18_matrix_eq]
  exact zero_18_matrix_posDef


private def zero_19_moment_0 : {v : ℝ // momentCoefficient 0 19 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_19_moment_1 : {v : ℝ // momentCoefficient 0 19 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_19_moment_2 : {v : ℝ // momentCoefficient 0 19 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_19_moment_3 : {v : ℝ // momentCoefficient 0 19 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_19_moment_4 : {v : ℝ // momentCoefficient 0 19 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_19_moment_5 : {v : ℝ // momentCoefficient 0 19 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_19_moment_6 : {v : ℝ // momentCoefficient 0 19 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_19_moment_7 : {v : ℝ // momentCoefficient 0 19 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_19_moment_8 : {v : ℝ // momentCoefficient 0 19 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_19_cell_00 : {v : ℝ // smallCoefficient 0 19 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_19_moment_0.property]
      dsimp only [zero_19_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_01 : {v : ℝ // smallCoefficient 0 19 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_19_moment_0.property,zero_19_moment_1.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_02 : {v : ℝ // smallCoefficient 0 19 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_03 : {v : ℝ // smallCoefficient 0 19 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_04 : {v : ℝ // smallCoefficient 0 19 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property,zero_19_moment_4.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3,zero_19_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_11 : {v : ℝ // smallCoefficient 0 19 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_12 : {v : ℝ // smallCoefficient 0 19 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_13 : {v : ℝ // smallCoefficient 0 19 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property,zero_19_moment_4.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3,zero_19_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_14 : {v : ℝ // smallCoefficient 0 19 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property,zero_19_moment_4.property,zero_19_moment_5.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3,zero_19_moment_4,zero_19_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_22 : {v : ℝ // smallCoefficient 0 19 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property,zero_19_moment_4.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3,zero_19_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_23 : {v : ℝ // smallCoefficient 0 19 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property,zero_19_moment_4.property,zero_19_moment_5.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3,zero_19_moment_4,zero_19_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_24 : {v : ℝ // smallCoefficient 0 19 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property,zero_19_moment_4.property,zero_19_moment_5.property,zero_19_moment_6.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3,zero_19_moment_4,zero_19_moment_5,zero_19_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_33 : {v : ℝ // smallCoefficient 0 19 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property,zero_19_moment_4.property,zero_19_moment_5.property,zero_19_moment_6.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3,zero_19_moment_4,zero_19_moment_5,zero_19_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_34 : {v : ℝ // smallCoefficient 0 19 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property,zero_19_moment_4.property,zero_19_moment_5.property,zero_19_moment_6.property,zero_19_moment_7.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3,zero_19_moment_4,zero_19_moment_5,zero_19_moment_6,zero_19_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_cell_44 : {v : ℝ // smallCoefficient 0 19 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_19_moment_0.property,zero_19_moment_1.property,zero_19_moment_2.property,zero_19_moment_3.property,zero_19_moment_4.property,zero_19_moment_5.property,zero_19_moment_6.property,zero_19_moment_7.property,zero_19_moment_8.property]
      dsimp only [zero_19_moment_0,zero_19_moment_1,zero_19_moment_2,zero_19_moment_3,zero_19_moment_4,zero_19_moment_5,zero_19_moment_6,zero_19_moment_7,zero_19_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_19_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_19_cell_00.val,zero_19_cell_01.val,zero_19_cell_02.val,zero_19_cell_03.val,zero_19_cell_04.val],
    ![zero_19_cell_01.val,zero_19_cell_11.val,zero_19_cell_12.val,zero_19_cell_13.val,zero_19_cell_14.val],
    ![zero_19_cell_02.val,zero_19_cell_12.val,zero_19_cell_22.val,zero_19_cell_23.val,zero_19_cell_24.val],
    ![zero_19_cell_03.val,zero_19_cell_13.val,zero_19_cell_23.val,zero_19_cell_33.val,zero_19_cell_34.val],
    ![zero_19_cell_04.val,zero_19_cell_14.val,zero_19_cell_24.val,zero_19_cell_34.val,zero_19_cell_44.val]]

private theorem zero_19_matrix_eq : smallCoefficient 0 19=zero_19_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_19_cell_00.property
  · exact zero_19_cell_01.property
  · exact zero_19_cell_02.property
  · exact zero_19_cell_03.property
  · exact zero_19_cell_04.property
  · exact (smallCoefficient_symmetric 0 19 1 0).trans zero_19_cell_01.property
  · exact zero_19_cell_11.property
  · exact zero_19_cell_12.property
  · exact zero_19_cell_13.property
  · exact zero_19_cell_14.property
  · exact (smallCoefficient_symmetric 0 19 2 0).trans zero_19_cell_02.property
  · exact (smallCoefficient_symmetric 0 19 2 1).trans zero_19_cell_12.property
  · exact zero_19_cell_22.property
  · exact zero_19_cell_23.property
  · exact zero_19_cell_24.property
  · exact (smallCoefficient_symmetric 0 19 3 0).trans zero_19_cell_03.property
  · exact (smallCoefficient_symmetric 0 19 3 1).trans zero_19_cell_13.property
  · exact (smallCoefficient_symmetric 0 19 3 2).trans zero_19_cell_23.property
  · exact zero_19_cell_33.property
  · exact zero_19_cell_34.property
  · exact (smallCoefficient_symmetric 0 19 4 0).trans zero_19_cell_04.property
  · exact (smallCoefficient_symmetric 0 19 4 1).trans zero_19_cell_14.property
  · exact (smallCoefficient_symmetric 0 19 4 2).trans zero_19_cell_24.property
  · exact (smallCoefficient_symmetric 0 19 4 3).trans zero_19_cell_34.property
  · exact zero_19_cell_44.property

private theorem zero_19_first_pos : 0 < zero_19_matrix 0 0 := by
  dsimp only [zero_19_matrix,zero_19_cell_00,zero_19_cell_01,zero_19_cell_02,zero_19_cell_03,zero_19_cell_04,zero_19_cell_11,zero_19_cell_12,zero_19_cell_13,zero_19_cell_14,zero_19_cell_22,zero_19_cell_23,zero_19_cell_24,zero_19_cell_33,zero_19_cell_34,zero_19_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_19_delta_pos : 0 < delta zero_19_matrix := by
  dsimp only [zero_19_matrix,zero_19_cell_00,zero_19_cell_01,zero_19_cell_02,zero_19_cell_03,zero_19_cell_04,zero_19_cell_11,zero_19_cell_12,zero_19_cell_13,zero_19_cell_14,zero_19_cell_22,zero_19_cell_23,zero_19_cell_24,zero_19_cell_33,zero_19_cell_34,zero_19_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_19_schur_pos : 0 < schur zero_19_matrix 0 0 := by
  dsimp only [zero_19_matrix,zero_19_cell_00,zero_19_cell_01,zero_19_cell_02,zero_19_cell_03,zero_19_cell_04,zero_19_cell_11,zero_19_cell_12,zero_19_cell_13,zero_19_cell_14,zero_19_cell_22,zero_19_cell_23,zero_19_cell_24,zero_19_cell_33,zero_19_cell_34,zero_19_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_19_minor_pos : 0 < minor zero_19_matrix := by
  dsimp only [zero_19_matrix,zero_19_cell_00,zero_19_cell_01,zero_19_cell_02,zero_19_cell_03,zero_19_cell_04,zero_19_cell_11,zero_19_cell_12,zero_19_cell_13,zero_19_cell_14,zero_19_cell_22,zero_19_cell_23,zero_19_cell_24,zero_19_cell_33,zero_19_cell_34,zero_19_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_19_det_pos : 0 < determinant zero_19_matrix := by
  dsimp only [zero_19_matrix,zero_19_cell_00,zero_19_cell_01,zero_19_cell_02,zero_19_cell_03,zero_19_cell_04,zero_19_cell_11,zero_19_cell_12,zero_19_cell_13,zero_19_cell_14,zero_19_cell_22,zero_19_cell_23,zero_19_cell_24,zero_19_cell_33,zero_19_cell_34,zero_19_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_19_matrix_posDef : zero_19_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_19_first_pos zero_19_delta_pos zero_19_schur_pos
    zero_19_minor_pos zero_19_det_pos
  intro i j
  rw [← zero_19_matrix_eq]
  exact smallCoefficient_symmetric 0 19 i j

private theorem zero_19_posDef : (smallCoefficient 0 19).PosDef := by
  rw [zero_19_matrix_eq]
  exact zero_19_matrix_posDef


private def zero_20_moment_0 : {v : ℝ // momentCoefficient 0 20 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_20_moment_1 : {v : ℝ // momentCoefficient 0 20 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_20_moment_2 : {v : ℝ // momentCoefficient 0 20 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_20_moment_3 : {v : ℝ // momentCoefficient 0 20 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_20_moment_4 : {v : ℝ // momentCoefficient 0 20 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_20_moment_5 : {v : ℝ // momentCoefficient 0 20 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_20_moment_6 : {v : ℝ // momentCoefficient 0 20 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_20_moment_7 : {v : ℝ // momentCoefficient 0 20 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_20_moment_8 : {v : ℝ // momentCoefficient 0 20 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_20_cell_00 : {v : ℝ // smallCoefficient 0 20 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_20_moment_0.property]
      dsimp only [zero_20_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_01 : {v : ℝ // smallCoefficient 0 20 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_20_moment_0.property,zero_20_moment_1.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_02 : {v : ℝ // smallCoefficient 0 20 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_03 : {v : ℝ // smallCoefficient 0 20 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_04 : {v : ℝ // smallCoefficient 0 20 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property,zero_20_moment_4.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3,zero_20_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_11 : {v : ℝ // smallCoefficient 0 20 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_12 : {v : ℝ // smallCoefficient 0 20 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_13 : {v : ℝ // smallCoefficient 0 20 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property,zero_20_moment_4.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3,zero_20_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_14 : {v : ℝ // smallCoefficient 0 20 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property,zero_20_moment_4.property,zero_20_moment_5.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3,zero_20_moment_4,zero_20_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_22 : {v : ℝ // smallCoefficient 0 20 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property,zero_20_moment_4.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3,zero_20_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_23 : {v : ℝ // smallCoefficient 0 20 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property,zero_20_moment_4.property,zero_20_moment_5.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3,zero_20_moment_4,zero_20_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_24 : {v : ℝ // smallCoefficient 0 20 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property,zero_20_moment_4.property,zero_20_moment_5.property,zero_20_moment_6.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3,zero_20_moment_4,zero_20_moment_5,zero_20_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_33 : {v : ℝ // smallCoefficient 0 20 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property,zero_20_moment_4.property,zero_20_moment_5.property,zero_20_moment_6.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3,zero_20_moment_4,zero_20_moment_5,zero_20_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_34 : {v : ℝ // smallCoefficient 0 20 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property,zero_20_moment_4.property,zero_20_moment_5.property,zero_20_moment_6.property,zero_20_moment_7.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3,zero_20_moment_4,zero_20_moment_5,zero_20_moment_6,zero_20_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_cell_44 : {v : ℝ // smallCoefficient 0 20 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_20_moment_0.property,zero_20_moment_1.property,zero_20_moment_2.property,zero_20_moment_3.property,zero_20_moment_4.property,zero_20_moment_5.property,zero_20_moment_6.property,zero_20_moment_7.property,zero_20_moment_8.property]
      dsimp only [zero_20_moment_0,zero_20_moment_1,zero_20_moment_2,zero_20_moment_3,zero_20_moment_4,zero_20_moment_5,zero_20_moment_6,zero_20_moment_7,zero_20_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_20_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_20_cell_00.val,zero_20_cell_01.val,zero_20_cell_02.val,zero_20_cell_03.val,zero_20_cell_04.val],
    ![zero_20_cell_01.val,zero_20_cell_11.val,zero_20_cell_12.val,zero_20_cell_13.val,zero_20_cell_14.val],
    ![zero_20_cell_02.val,zero_20_cell_12.val,zero_20_cell_22.val,zero_20_cell_23.val,zero_20_cell_24.val],
    ![zero_20_cell_03.val,zero_20_cell_13.val,zero_20_cell_23.val,zero_20_cell_33.val,zero_20_cell_34.val],
    ![zero_20_cell_04.val,zero_20_cell_14.val,zero_20_cell_24.val,zero_20_cell_34.val,zero_20_cell_44.val]]

private theorem zero_20_matrix_eq : smallCoefficient 0 20=zero_20_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_20_cell_00.property
  · exact zero_20_cell_01.property
  · exact zero_20_cell_02.property
  · exact zero_20_cell_03.property
  · exact zero_20_cell_04.property
  · exact (smallCoefficient_symmetric 0 20 1 0).trans zero_20_cell_01.property
  · exact zero_20_cell_11.property
  · exact zero_20_cell_12.property
  · exact zero_20_cell_13.property
  · exact zero_20_cell_14.property
  · exact (smallCoefficient_symmetric 0 20 2 0).trans zero_20_cell_02.property
  · exact (smallCoefficient_symmetric 0 20 2 1).trans zero_20_cell_12.property
  · exact zero_20_cell_22.property
  · exact zero_20_cell_23.property
  · exact zero_20_cell_24.property
  · exact (smallCoefficient_symmetric 0 20 3 0).trans zero_20_cell_03.property
  · exact (smallCoefficient_symmetric 0 20 3 1).trans zero_20_cell_13.property
  · exact (smallCoefficient_symmetric 0 20 3 2).trans zero_20_cell_23.property
  · exact zero_20_cell_33.property
  · exact zero_20_cell_34.property
  · exact (smallCoefficient_symmetric 0 20 4 0).trans zero_20_cell_04.property
  · exact (smallCoefficient_symmetric 0 20 4 1).trans zero_20_cell_14.property
  · exact (smallCoefficient_symmetric 0 20 4 2).trans zero_20_cell_24.property
  · exact (smallCoefficient_symmetric 0 20 4 3).trans zero_20_cell_34.property
  · exact zero_20_cell_44.property

private theorem zero_20_first_pos : 0 < zero_20_matrix 0 0 := by
  dsimp only [zero_20_matrix,zero_20_cell_00,zero_20_cell_01,zero_20_cell_02,zero_20_cell_03,zero_20_cell_04,zero_20_cell_11,zero_20_cell_12,zero_20_cell_13,zero_20_cell_14,zero_20_cell_22,zero_20_cell_23,zero_20_cell_24,zero_20_cell_33,zero_20_cell_34,zero_20_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_20_delta_pos : 0 < delta zero_20_matrix := by
  dsimp only [zero_20_matrix,zero_20_cell_00,zero_20_cell_01,zero_20_cell_02,zero_20_cell_03,zero_20_cell_04,zero_20_cell_11,zero_20_cell_12,zero_20_cell_13,zero_20_cell_14,zero_20_cell_22,zero_20_cell_23,zero_20_cell_24,zero_20_cell_33,zero_20_cell_34,zero_20_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_20_schur_pos : 0 < schur zero_20_matrix 0 0 := by
  dsimp only [zero_20_matrix,zero_20_cell_00,zero_20_cell_01,zero_20_cell_02,zero_20_cell_03,zero_20_cell_04,zero_20_cell_11,zero_20_cell_12,zero_20_cell_13,zero_20_cell_14,zero_20_cell_22,zero_20_cell_23,zero_20_cell_24,zero_20_cell_33,zero_20_cell_34,zero_20_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_20_minor_pos : 0 < minor zero_20_matrix := by
  dsimp only [zero_20_matrix,zero_20_cell_00,zero_20_cell_01,zero_20_cell_02,zero_20_cell_03,zero_20_cell_04,zero_20_cell_11,zero_20_cell_12,zero_20_cell_13,zero_20_cell_14,zero_20_cell_22,zero_20_cell_23,zero_20_cell_24,zero_20_cell_33,zero_20_cell_34,zero_20_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_20_det_pos : 0 < determinant zero_20_matrix := by
  dsimp only [zero_20_matrix,zero_20_cell_00,zero_20_cell_01,zero_20_cell_02,zero_20_cell_03,zero_20_cell_04,zero_20_cell_11,zero_20_cell_12,zero_20_cell_13,zero_20_cell_14,zero_20_cell_22,zero_20_cell_23,zero_20_cell_24,zero_20_cell_33,zero_20_cell_34,zero_20_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_20_matrix_posDef : zero_20_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_20_first_pos zero_20_delta_pos zero_20_schur_pos
    zero_20_minor_pos zero_20_det_pos
  intro i j
  rw [← zero_20_matrix_eq]
  exact smallCoefficient_symmetric 0 20 i j

private theorem zero_20_posDef : (smallCoefficient 0 20).PosDef := by
  rw [zero_20_matrix_eq]
  exact zero_20_matrix_posDef


private def zero_21_moment_0 : {v : ℝ // momentCoefficient 0 21 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_21_moment_1 : {v : ℝ // momentCoefficient 0 21 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_21_moment_2 : {v : ℝ // momentCoefficient 0 21 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_21_moment_3 : {v : ℝ // momentCoefficient 0 21 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_21_moment_4 : {v : ℝ // momentCoefficient 0 21 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_21_moment_5 : {v : ℝ // momentCoefficient 0 21 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_21_moment_6 : {v : ℝ // momentCoefficient 0 21 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_21_moment_7 : {v : ℝ // momentCoefficient 0 21 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_21_moment_8 : {v : ℝ // momentCoefficient 0 21 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_21_cell_00 : {v : ℝ // smallCoefficient 0 21 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_21_moment_0.property]
      dsimp only [zero_21_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_01 : {v : ℝ // smallCoefficient 0 21 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_21_moment_0.property,zero_21_moment_1.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_02 : {v : ℝ // smallCoefficient 0 21 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_03 : {v : ℝ // smallCoefficient 0 21 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_04 : {v : ℝ // smallCoefficient 0 21 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property,zero_21_moment_4.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3,zero_21_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_11 : {v : ℝ // smallCoefficient 0 21 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_12 : {v : ℝ // smallCoefficient 0 21 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_13 : {v : ℝ // smallCoefficient 0 21 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property,zero_21_moment_4.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3,zero_21_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_14 : {v : ℝ // smallCoefficient 0 21 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property,zero_21_moment_4.property,zero_21_moment_5.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3,zero_21_moment_4,zero_21_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_22 : {v : ℝ // smallCoefficient 0 21 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property,zero_21_moment_4.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3,zero_21_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_23 : {v : ℝ // smallCoefficient 0 21 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property,zero_21_moment_4.property,zero_21_moment_5.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3,zero_21_moment_4,zero_21_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_24 : {v : ℝ // smallCoefficient 0 21 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property,zero_21_moment_4.property,zero_21_moment_5.property,zero_21_moment_6.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3,zero_21_moment_4,zero_21_moment_5,zero_21_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_33 : {v : ℝ // smallCoefficient 0 21 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property,zero_21_moment_4.property,zero_21_moment_5.property,zero_21_moment_6.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3,zero_21_moment_4,zero_21_moment_5,zero_21_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_34 : {v : ℝ // smallCoefficient 0 21 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property,zero_21_moment_4.property,zero_21_moment_5.property,zero_21_moment_6.property,zero_21_moment_7.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3,zero_21_moment_4,zero_21_moment_5,zero_21_moment_6,zero_21_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_cell_44 : {v : ℝ // smallCoefficient 0 21 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_21_moment_0.property,zero_21_moment_1.property,zero_21_moment_2.property,zero_21_moment_3.property,zero_21_moment_4.property,zero_21_moment_5.property,zero_21_moment_6.property,zero_21_moment_7.property,zero_21_moment_8.property]
      dsimp only [zero_21_moment_0,zero_21_moment_1,zero_21_moment_2,zero_21_moment_3,zero_21_moment_4,zero_21_moment_5,zero_21_moment_6,zero_21_moment_7,zero_21_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_21_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_21_cell_00.val,zero_21_cell_01.val,zero_21_cell_02.val,zero_21_cell_03.val,zero_21_cell_04.val],
    ![zero_21_cell_01.val,zero_21_cell_11.val,zero_21_cell_12.val,zero_21_cell_13.val,zero_21_cell_14.val],
    ![zero_21_cell_02.val,zero_21_cell_12.val,zero_21_cell_22.val,zero_21_cell_23.val,zero_21_cell_24.val],
    ![zero_21_cell_03.val,zero_21_cell_13.val,zero_21_cell_23.val,zero_21_cell_33.val,zero_21_cell_34.val],
    ![zero_21_cell_04.val,zero_21_cell_14.val,zero_21_cell_24.val,zero_21_cell_34.val,zero_21_cell_44.val]]

private theorem zero_21_matrix_eq : smallCoefficient 0 21=zero_21_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_21_cell_00.property
  · exact zero_21_cell_01.property
  · exact zero_21_cell_02.property
  · exact zero_21_cell_03.property
  · exact zero_21_cell_04.property
  · exact (smallCoefficient_symmetric 0 21 1 0).trans zero_21_cell_01.property
  · exact zero_21_cell_11.property
  · exact zero_21_cell_12.property
  · exact zero_21_cell_13.property
  · exact zero_21_cell_14.property
  · exact (smallCoefficient_symmetric 0 21 2 0).trans zero_21_cell_02.property
  · exact (smallCoefficient_symmetric 0 21 2 1).trans zero_21_cell_12.property
  · exact zero_21_cell_22.property
  · exact zero_21_cell_23.property
  · exact zero_21_cell_24.property
  · exact (smallCoefficient_symmetric 0 21 3 0).trans zero_21_cell_03.property
  · exact (smallCoefficient_symmetric 0 21 3 1).trans zero_21_cell_13.property
  · exact (smallCoefficient_symmetric 0 21 3 2).trans zero_21_cell_23.property
  · exact zero_21_cell_33.property
  · exact zero_21_cell_34.property
  · exact (smallCoefficient_symmetric 0 21 4 0).trans zero_21_cell_04.property
  · exact (smallCoefficient_symmetric 0 21 4 1).trans zero_21_cell_14.property
  · exact (smallCoefficient_symmetric 0 21 4 2).trans zero_21_cell_24.property
  · exact (smallCoefficient_symmetric 0 21 4 3).trans zero_21_cell_34.property
  · exact zero_21_cell_44.property

private theorem zero_21_first_pos : 0 < zero_21_matrix 0 0 := by
  dsimp only [zero_21_matrix,zero_21_cell_00,zero_21_cell_01,zero_21_cell_02,zero_21_cell_03,zero_21_cell_04,zero_21_cell_11,zero_21_cell_12,zero_21_cell_13,zero_21_cell_14,zero_21_cell_22,zero_21_cell_23,zero_21_cell_24,zero_21_cell_33,zero_21_cell_34,zero_21_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_21_delta_pos : 0 < delta zero_21_matrix := by
  dsimp only [zero_21_matrix,zero_21_cell_00,zero_21_cell_01,zero_21_cell_02,zero_21_cell_03,zero_21_cell_04,zero_21_cell_11,zero_21_cell_12,zero_21_cell_13,zero_21_cell_14,zero_21_cell_22,zero_21_cell_23,zero_21_cell_24,zero_21_cell_33,zero_21_cell_34,zero_21_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_21_schur_pos : 0 < schur zero_21_matrix 0 0 := by
  dsimp only [zero_21_matrix,zero_21_cell_00,zero_21_cell_01,zero_21_cell_02,zero_21_cell_03,zero_21_cell_04,zero_21_cell_11,zero_21_cell_12,zero_21_cell_13,zero_21_cell_14,zero_21_cell_22,zero_21_cell_23,zero_21_cell_24,zero_21_cell_33,zero_21_cell_34,zero_21_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_21_minor_pos : 0 < minor zero_21_matrix := by
  dsimp only [zero_21_matrix,zero_21_cell_00,zero_21_cell_01,zero_21_cell_02,zero_21_cell_03,zero_21_cell_04,zero_21_cell_11,zero_21_cell_12,zero_21_cell_13,zero_21_cell_14,zero_21_cell_22,zero_21_cell_23,zero_21_cell_24,zero_21_cell_33,zero_21_cell_34,zero_21_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_21_det_pos : 0 < determinant zero_21_matrix := by
  dsimp only [zero_21_matrix,zero_21_cell_00,zero_21_cell_01,zero_21_cell_02,zero_21_cell_03,zero_21_cell_04,zero_21_cell_11,zero_21_cell_12,zero_21_cell_13,zero_21_cell_14,zero_21_cell_22,zero_21_cell_23,zero_21_cell_24,zero_21_cell_33,zero_21_cell_34,zero_21_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_21_matrix_posDef : zero_21_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_21_first_pos zero_21_delta_pos zero_21_schur_pos
    zero_21_minor_pos zero_21_det_pos
  intro i j
  rw [← zero_21_matrix_eq]
  exact smallCoefficient_symmetric 0 21 i j

private theorem zero_21_posDef : (smallCoefficient 0 21).PosDef := by
  rw [zero_21_matrix_eq]
  exact zero_21_matrix_posDef


private def zero_22_moment_0 : {v : ℝ // momentCoefficient 0 22 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_22_moment_1 : {v : ℝ // momentCoefficient 0 22 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_22_moment_2 : {v : ℝ // momentCoefficient 0 22 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_22_moment_3 : {v : ℝ // momentCoefficient 0 22 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_22_moment_4 : {v : ℝ // momentCoefficient 0 22 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_22_moment_5 : {v : ℝ // momentCoefficient 0 22 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_22_moment_6 : {v : ℝ // momentCoefficient 0 22 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_22_moment_7 : {v : ℝ // momentCoefficient 0 22 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_22_moment_8 : {v : ℝ // momentCoefficient 0 22 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_22_cell_00 : {v : ℝ // smallCoefficient 0 22 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_22_moment_0.property]
      dsimp only [zero_22_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_01 : {v : ℝ // smallCoefficient 0 22 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_22_moment_0.property,zero_22_moment_1.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_02 : {v : ℝ // smallCoefficient 0 22 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_03 : {v : ℝ // smallCoefficient 0 22 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_04 : {v : ℝ // smallCoefficient 0 22 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property,zero_22_moment_4.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3,zero_22_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_11 : {v : ℝ // smallCoefficient 0 22 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_12 : {v : ℝ // smallCoefficient 0 22 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_13 : {v : ℝ // smallCoefficient 0 22 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property,zero_22_moment_4.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3,zero_22_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_14 : {v : ℝ // smallCoefficient 0 22 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property,zero_22_moment_4.property,zero_22_moment_5.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3,zero_22_moment_4,zero_22_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_22 : {v : ℝ // smallCoefficient 0 22 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property,zero_22_moment_4.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3,zero_22_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_23 : {v : ℝ // smallCoefficient 0 22 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property,zero_22_moment_4.property,zero_22_moment_5.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3,zero_22_moment_4,zero_22_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_24 : {v : ℝ // smallCoefficient 0 22 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property,zero_22_moment_4.property,zero_22_moment_5.property,zero_22_moment_6.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3,zero_22_moment_4,zero_22_moment_5,zero_22_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_33 : {v : ℝ // smallCoefficient 0 22 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property,zero_22_moment_4.property,zero_22_moment_5.property,zero_22_moment_6.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3,zero_22_moment_4,zero_22_moment_5,zero_22_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_34 : {v : ℝ // smallCoefficient 0 22 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property,zero_22_moment_4.property,zero_22_moment_5.property,zero_22_moment_6.property,zero_22_moment_7.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3,zero_22_moment_4,zero_22_moment_5,zero_22_moment_6,zero_22_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_cell_44 : {v : ℝ // smallCoefficient 0 22 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_22_moment_0.property,zero_22_moment_1.property,zero_22_moment_2.property,zero_22_moment_3.property,zero_22_moment_4.property,zero_22_moment_5.property,zero_22_moment_6.property,zero_22_moment_7.property,zero_22_moment_8.property]
      dsimp only [zero_22_moment_0,zero_22_moment_1,zero_22_moment_2,zero_22_moment_3,zero_22_moment_4,zero_22_moment_5,zero_22_moment_6,zero_22_moment_7,zero_22_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_22_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_22_cell_00.val,zero_22_cell_01.val,zero_22_cell_02.val,zero_22_cell_03.val,zero_22_cell_04.val],
    ![zero_22_cell_01.val,zero_22_cell_11.val,zero_22_cell_12.val,zero_22_cell_13.val,zero_22_cell_14.val],
    ![zero_22_cell_02.val,zero_22_cell_12.val,zero_22_cell_22.val,zero_22_cell_23.val,zero_22_cell_24.val],
    ![zero_22_cell_03.val,zero_22_cell_13.val,zero_22_cell_23.val,zero_22_cell_33.val,zero_22_cell_34.val],
    ![zero_22_cell_04.val,zero_22_cell_14.val,zero_22_cell_24.val,zero_22_cell_34.val,zero_22_cell_44.val]]

private theorem zero_22_matrix_eq : smallCoefficient 0 22=zero_22_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_22_cell_00.property
  · exact zero_22_cell_01.property
  · exact zero_22_cell_02.property
  · exact zero_22_cell_03.property
  · exact zero_22_cell_04.property
  · exact (smallCoefficient_symmetric 0 22 1 0).trans zero_22_cell_01.property
  · exact zero_22_cell_11.property
  · exact zero_22_cell_12.property
  · exact zero_22_cell_13.property
  · exact zero_22_cell_14.property
  · exact (smallCoefficient_symmetric 0 22 2 0).trans zero_22_cell_02.property
  · exact (smallCoefficient_symmetric 0 22 2 1).trans zero_22_cell_12.property
  · exact zero_22_cell_22.property
  · exact zero_22_cell_23.property
  · exact zero_22_cell_24.property
  · exact (smallCoefficient_symmetric 0 22 3 0).trans zero_22_cell_03.property
  · exact (smallCoefficient_symmetric 0 22 3 1).trans zero_22_cell_13.property
  · exact (smallCoefficient_symmetric 0 22 3 2).trans zero_22_cell_23.property
  · exact zero_22_cell_33.property
  · exact zero_22_cell_34.property
  · exact (smallCoefficient_symmetric 0 22 4 0).trans zero_22_cell_04.property
  · exact (smallCoefficient_symmetric 0 22 4 1).trans zero_22_cell_14.property
  · exact (smallCoefficient_symmetric 0 22 4 2).trans zero_22_cell_24.property
  · exact (smallCoefficient_symmetric 0 22 4 3).trans zero_22_cell_34.property
  · exact zero_22_cell_44.property

private theorem zero_22_first_pos : 0 < zero_22_matrix 0 0 := by
  dsimp only [zero_22_matrix,zero_22_cell_00,zero_22_cell_01,zero_22_cell_02,zero_22_cell_03,zero_22_cell_04,zero_22_cell_11,zero_22_cell_12,zero_22_cell_13,zero_22_cell_14,zero_22_cell_22,zero_22_cell_23,zero_22_cell_24,zero_22_cell_33,zero_22_cell_34,zero_22_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_22_delta_pos : 0 < delta zero_22_matrix := by
  dsimp only [zero_22_matrix,zero_22_cell_00,zero_22_cell_01,zero_22_cell_02,zero_22_cell_03,zero_22_cell_04,zero_22_cell_11,zero_22_cell_12,zero_22_cell_13,zero_22_cell_14,zero_22_cell_22,zero_22_cell_23,zero_22_cell_24,zero_22_cell_33,zero_22_cell_34,zero_22_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_22_schur_pos : 0 < schur zero_22_matrix 0 0 := by
  dsimp only [zero_22_matrix,zero_22_cell_00,zero_22_cell_01,zero_22_cell_02,zero_22_cell_03,zero_22_cell_04,zero_22_cell_11,zero_22_cell_12,zero_22_cell_13,zero_22_cell_14,zero_22_cell_22,zero_22_cell_23,zero_22_cell_24,zero_22_cell_33,zero_22_cell_34,zero_22_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_22_minor_pos : 0 < minor zero_22_matrix := by
  dsimp only [zero_22_matrix,zero_22_cell_00,zero_22_cell_01,zero_22_cell_02,zero_22_cell_03,zero_22_cell_04,zero_22_cell_11,zero_22_cell_12,zero_22_cell_13,zero_22_cell_14,zero_22_cell_22,zero_22_cell_23,zero_22_cell_24,zero_22_cell_33,zero_22_cell_34,zero_22_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_22_det_pos : 0 < determinant zero_22_matrix := by
  dsimp only [zero_22_matrix,zero_22_cell_00,zero_22_cell_01,zero_22_cell_02,zero_22_cell_03,zero_22_cell_04,zero_22_cell_11,zero_22_cell_12,zero_22_cell_13,zero_22_cell_14,zero_22_cell_22,zero_22_cell_23,zero_22_cell_24,zero_22_cell_33,zero_22_cell_34,zero_22_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_22_matrix_posDef : zero_22_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_22_first_pos zero_22_delta_pos zero_22_schur_pos
    zero_22_minor_pos zero_22_det_pos
  intro i j
  rw [← zero_22_matrix_eq]
  exact smallCoefficient_symmetric 0 22 i j

private theorem zero_22_posDef : (smallCoefficient 0 22).PosDef := by
  rw [zero_22_matrix_eq]
  exact zero_22_matrix_posDef


private def zero_23_moment_0 : {v : ℝ // momentCoefficient 0 23 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_23_moment_1 : {v : ℝ // momentCoefficient 0 23 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_23_moment_2 : {v : ℝ // momentCoefficient 0 23 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_23_moment_3 : {v : ℝ // momentCoefficient 0 23 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_23_moment_4 : {v : ℝ // momentCoefficient 0 23 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_23_moment_5 : {v : ℝ // momentCoefficient 0 23 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_23_moment_6 : {v : ℝ // momentCoefficient 0 23 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_23_moment_7 : {v : ℝ // momentCoefficient 0 23 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_23_moment_8 : {v : ℝ // momentCoefficient 0 23 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_23_cell_00 : {v : ℝ // smallCoefficient 0 23 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_23_moment_0.property]
      dsimp only [zero_23_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_01 : {v : ℝ // smallCoefficient 0 23 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_23_moment_0.property,zero_23_moment_1.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_02 : {v : ℝ // smallCoefficient 0 23 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_03 : {v : ℝ // smallCoefficient 0 23 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_04 : {v : ℝ // smallCoefficient 0 23 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property,zero_23_moment_4.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3,zero_23_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_11 : {v : ℝ // smallCoefficient 0 23 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_12 : {v : ℝ // smallCoefficient 0 23 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_13 : {v : ℝ // smallCoefficient 0 23 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property,zero_23_moment_4.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3,zero_23_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_14 : {v : ℝ // smallCoefficient 0 23 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property,zero_23_moment_4.property,zero_23_moment_5.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3,zero_23_moment_4,zero_23_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_22 : {v : ℝ // smallCoefficient 0 23 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property,zero_23_moment_4.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3,zero_23_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_23 : {v : ℝ // smallCoefficient 0 23 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property,zero_23_moment_4.property,zero_23_moment_5.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3,zero_23_moment_4,zero_23_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_24 : {v : ℝ // smallCoefficient 0 23 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property,zero_23_moment_4.property,zero_23_moment_5.property,zero_23_moment_6.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3,zero_23_moment_4,zero_23_moment_5,zero_23_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_33 : {v : ℝ // smallCoefficient 0 23 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property,zero_23_moment_4.property,zero_23_moment_5.property,zero_23_moment_6.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3,zero_23_moment_4,zero_23_moment_5,zero_23_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_34 : {v : ℝ // smallCoefficient 0 23 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property,zero_23_moment_4.property,zero_23_moment_5.property,zero_23_moment_6.property,zero_23_moment_7.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3,zero_23_moment_4,zero_23_moment_5,zero_23_moment_6,zero_23_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_cell_44 : {v : ℝ // smallCoefficient 0 23 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_23_moment_0.property,zero_23_moment_1.property,zero_23_moment_2.property,zero_23_moment_3.property,zero_23_moment_4.property,zero_23_moment_5.property,zero_23_moment_6.property,zero_23_moment_7.property,zero_23_moment_8.property]
      dsimp only [zero_23_moment_0,zero_23_moment_1,zero_23_moment_2,zero_23_moment_3,zero_23_moment_4,zero_23_moment_5,zero_23_moment_6,zero_23_moment_7,zero_23_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_23_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_23_cell_00.val,zero_23_cell_01.val,zero_23_cell_02.val,zero_23_cell_03.val,zero_23_cell_04.val],
    ![zero_23_cell_01.val,zero_23_cell_11.val,zero_23_cell_12.val,zero_23_cell_13.val,zero_23_cell_14.val],
    ![zero_23_cell_02.val,zero_23_cell_12.val,zero_23_cell_22.val,zero_23_cell_23.val,zero_23_cell_24.val],
    ![zero_23_cell_03.val,zero_23_cell_13.val,zero_23_cell_23.val,zero_23_cell_33.val,zero_23_cell_34.val],
    ![zero_23_cell_04.val,zero_23_cell_14.val,zero_23_cell_24.val,zero_23_cell_34.val,zero_23_cell_44.val]]

private theorem zero_23_matrix_eq : smallCoefficient 0 23=zero_23_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_23_cell_00.property
  · exact zero_23_cell_01.property
  · exact zero_23_cell_02.property
  · exact zero_23_cell_03.property
  · exact zero_23_cell_04.property
  · exact (smallCoefficient_symmetric 0 23 1 0).trans zero_23_cell_01.property
  · exact zero_23_cell_11.property
  · exact zero_23_cell_12.property
  · exact zero_23_cell_13.property
  · exact zero_23_cell_14.property
  · exact (smallCoefficient_symmetric 0 23 2 0).trans zero_23_cell_02.property
  · exact (smallCoefficient_symmetric 0 23 2 1).trans zero_23_cell_12.property
  · exact zero_23_cell_22.property
  · exact zero_23_cell_23.property
  · exact zero_23_cell_24.property
  · exact (smallCoefficient_symmetric 0 23 3 0).trans zero_23_cell_03.property
  · exact (smallCoefficient_symmetric 0 23 3 1).trans zero_23_cell_13.property
  · exact (smallCoefficient_symmetric 0 23 3 2).trans zero_23_cell_23.property
  · exact zero_23_cell_33.property
  · exact zero_23_cell_34.property
  · exact (smallCoefficient_symmetric 0 23 4 0).trans zero_23_cell_04.property
  · exact (smallCoefficient_symmetric 0 23 4 1).trans zero_23_cell_14.property
  · exact (smallCoefficient_symmetric 0 23 4 2).trans zero_23_cell_24.property
  · exact (smallCoefficient_symmetric 0 23 4 3).trans zero_23_cell_34.property
  · exact zero_23_cell_44.property

private theorem zero_23_first_pos : 0 < zero_23_matrix 0 0 := by
  dsimp only [zero_23_matrix,zero_23_cell_00,zero_23_cell_01,zero_23_cell_02,zero_23_cell_03,zero_23_cell_04,zero_23_cell_11,zero_23_cell_12,zero_23_cell_13,zero_23_cell_14,zero_23_cell_22,zero_23_cell_23,zero_23_cell_24,zero_23_cell_33,zero_23_cell_34,zero_23_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_23_delta_pos : 0 < delta zero_23_matrix := by
  dsimp only [zero_23_matrix,zero_23_cell_00,zero_23_cell_01,zero_23_cell_02,zero_23_cell_03,zero_23_cell_04,zero_23_cell_11,zero_23_cell_12,zero_23_cell_13,zero_23_cell_14,zero_23_cell_22,zero_23_cell_23,zero_23_cell_24,zero_23_cell_33,zero_23_cell_34,zero_23_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_23_schur_pos : 0 < schur zero_23_matrix 0 0 := by
  dsimp only [zero_23_matrix,zero_23_cell_00,zero_23_cell_01,zero_23_cell_02,zero_23_cell_03,zero_23_cell_04,zero_23_cell_11,zero_23_cell_12,zero_23_cell_13,zero_23_cell_14,zero_23_cell_22,zero_23_cell_23,zero_23_cell_24,zero_23_cell_33,zero_23_cell_34,zero_23_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_23_minor_pos : 0 < minor zero_23_matrix := by
  dsimp only [zero_23_matrix,zero_23_cell_00,zero_23_cell_01,zero_23_cell_02,zero_23_cell_03,zero_23_cell_04,zero_23_cell_11,zero_23_cell_12,zero_23_cell_13,zero_23_cell_14,zero_23_cell_22,zero_23_cell_23,zero_23_cell_24,zero_23_cell_33,zero_23_cell_34,zero_23_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_23_det_pos : 0 < determinant zero_23_matrix := by
  dsimp only [zero_23_matrix,zero_23_cell_00,zero_23_cell_01,zero_23_cell_02,zero_23_cell_03,zero_23_cell_04,zero_23_cell_11,zero_23_cell_12,zero_23_cell_13,zero_23_cell_14,zero_23_cell_22,zero_23_cell_23,zero_23_cell_24,zero_23_cell_33,zero_23_cell_34,zero_23_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_23_matrix_posDef : zero_23_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_23_first_pos zero_23_delta_pos zero_23_schur_pos
    zero_23_minor_pos zero_23_det_pos
  intro i j
  rw [← zero_23_matrix_eq]
  exact smallCoefficient_symmetric 0 23 i j

private theorem zero_23_posDef : (smallCoefficient 0 23).PosDef := by
  rw [zero_23_matrix_eq]
  exact zero_23_matrix_posDef


private def zero_24_moment_0 : {v : ℝ // momentCoefficient 0 24 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_24_moment_1 : {v : ℝ // momentCoefficient 0 24 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_24_moment_2 : {v : ℝ // momentCoefficient 0 24 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_24_moment_3 : {v : ℝ // momentCoefficient 0 24 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_24_moment_4 : {v : ℝ // momentCoefficient 0 24 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_24_moment_5 : {v : ℝ // momentCoefficient 0 24 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_24_moment_6 : {v : ℝ // momentCoefficient 0 24 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_24_moment_7 : {v : ℝ // momentCoefficient 0 24 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_24_moment_8 : {v : ℝ // momentCoefficient 0 24 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_24_cell_00 : {v : ℝ // smallCoefficient 0 24 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_24_moment_0.property]
      dsimp only [zero_24_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_01 : {v : ℝ // smallCoefficient 0 24 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_24_moment_0.property,zero_24_moment_1.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_02 : {v : ℝ // smallCoefficient 0 24 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_03 : {v : ℝ // smallCoefficient 0 24 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_04 : {v : ℝ // smallCoefficient 0 24 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property,zero_24_moment_4.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3,zero_24_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_11 : {v : ℝ // smallCoefficient 0 24 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_12 : {v : ℝ // smallCoefficient 0 24 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_13 : {v : ℝ // smallCoefficient 0 24 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property,zero_24_moment_4.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3,zero_24_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_14 : {v : ℝ // smallCoefficient 0 24 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property,zero_24_moment_4.property,zero_24_moment_5.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3,zero_24_moment_4,zero_24_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_22 : {v : ℝ // smallCoefficient 0 24 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property,zero_24_moment_4.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3,zero_24_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_23 : {v : ℝ // smallCoefficient 0 24 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property,zero_24_moment_4.property,zero_24_moment_5.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3,zero_24_moment_4,zero_24_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_24 : {v : ℝ // smallCoefficient 0 24 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property,zero_24_moment_4.property,zero_24_moment_5.property,zero_24_moment_6.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3,zero_24_moment_4,zero_24_moment_5,zero_24_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_33 : {v : ℝ // smallCoefficient 0 24 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property,zero_24_moment_4.property,zero_24_moment_5.property,zero_24_moment_6.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3,zero_24_moment_4,zero_24_moment_5,zero_24_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_34 : {v : ℝ // smallCoefficient 0 24 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property,zero_24_moment_4.property,zero_24_moment_5.property,zero_24_moment_6.property,zero_24_moment_7.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3,zero_24_moment_4,zero_24_moment_5,zero_24_moment_6,zero_24_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_cell_44 : {v : ℝ // smallCoefficient 0 24 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_24_moment_0.property,zero_24_moment_1.property,zero_24_moment_2.property,zero_24_moment_3.property,zero_24_moment_4.property,zero_24_moment_5.property,zero_24_moment_6.property,zero_24_moment_7.property,zero_24_moment_8.property]
      dsimp only [zero_24_moment_0,zero_24_moment_1,zero_24_moment_2,zero_24_moment_3,zero_24_moment_4,zero_24_moment_5,zero_24_moment_6,zero_24_moment_7,zero_24_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_24_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_24_cell_00.val,zero_24_cell_01.val,zero_24_cell_02.val,zero_24_cell_03.val,zero_24_cell_04.val],
    ![zero_24_cell_01.val,zero_24_cell_11.val,zero_24_cell_12.val,zero_24_cell_13.val,zero_24_cell_14.val],
    ![zero_24_cell_02.val,zero_24_cell_12.val,zero_24_cell_22.val,zero_24_cell_23.val,zero_24_cell_24.val],
    ![zero_24_cell_03.val,zero_24_cell_13.val,zero_24_cell_23.val,zero_24_cell_33.val,zero_24_cell_34.val],
    ![zero_24_cell_04.val,zero_24_cell_14.val,zero_24_cell_24.val,zero_24_cell_34.val,zero_24_cell_44.val]]

private theorem zero_24_matrix_eq : smallCoefficient 0 24=zero_24_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_24_cell_00.property
  · exact zero_24_cell_01.property
  · exact zero_24_cell_02.property
  · exact zero_24_cell_03.property
  · exact zero_24_cell_04.property
  · exact (smallCoefficient_symmetric 0 24 1 0).trans zero_24_cell_01.property
  · exact zero_24_cell_11.property
  · exact zero_24_cell_12.property
  · exact zero_24_cell_13.property
  · exact zero_24_cell_14.property
  · exact (smallCoefficient_symmetric 0 24 2 0).trans zero_24_cell_02.property
  · exact (smallCoefficient_symmetric 0 24 2 1).trans zero_24_cell_12.property
  · exact zero_24_cell_22.property
  · exact zero_24_cell_23.property
  · exact zero_24_cell_24.property
  · exact (smallCoefficient_symmetric 0 24 3 0).trans zero_24_cell_03.property
  · exact (smallCoefficient_symmetric 0 24 3 1).trans zero_24_cell_13.property
  · exact (smallCoefficient_symmetric 0 24 3 2).trans zero_24_cell_23.property
  · exact zero_24_cell_33.property
  · exact zero_24_cell_34.property
  · exact (smallCoefficient_symmetric 0 24 4 0).trans zero_24_cell_04.property
  · exact (smallCoefficient_symmetric 0 24 4 1).trans zero_24_cell_14.property
  · exact (smallCoefficient_symmetric 0 24 4 2).trans zero_24_cell_24.property
  · exact (smallCoefficient_symmetric 0 24 4 3).trans zero_24_cell_34.property
  · exact zero_24_cell_44.property

private theorem zero_24_first_pos : 0 < zero_24_matrix 0 0 := by
  dsimp only [zero_24_matrix,zero_24_cell_00,zero_24_cell_01,zero_24_cell_02,zero_24_cell_03,zero_24_cell_04,zero_24_cell_11,zero_24_cell_12,zero_24_cell_13,zero_24_cell_14,zero_24_cell_22,zero_24_cell_23,zero_24_cell_24,zero_24_cell_33,zero_24_cell_34,zero_24_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_24_delta_pos : 0 < delta zero_24_matrix := by
  dsimp only [zero_24_matrix,zero_24_cell_00,zero_24_cell_01,zero_24_cell_02,zero_24_cell_03,zero_24_cell_04,zero_24_cell_11,zero_24_cell_12,zero_24_cell_13,zero_24_cell_14,zero_24_cell_22,zero_24_cell_23,zero_24_cell_24,zero_24_cell_33,zero_24_cell_34,zero_24_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_24_schur_pos : 0 < schur zero_24_matrix 0 0 := by
  dsimp only [zero_24_matrix,zero_24_cell_00,zero_24_cell_01,zero_24_cell_02,zero_24_cell_03,zero_24_cell_04,zero_24_cell_11,zero_24_cell_12,zero_24_cell_13,zero_24_cell_14,zero_24_cell_22,zero_24_cell_23,zero_24_cell_24,zero_24_cell_33,zero_24_cell_34,zero_24_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_24_minor_pos : 0 < minor zero_24_matrix := by
  dsimp only [zero_24_matrix,zero_24_cell_00,zero_24_cell_01,zero_24_cell_02,zero_24_cell_03,zero_24_cell_04,zero_24_cell_11,zero_24_cell_12,zero_24_cell_13,zero_24_cell_14,zero_24_cell_22,zero_24_cell_23,zero_24_cell_24,zero_24_cell_33,zero_24_cell_34,zero_24_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_24_det_pos : 0 < determinant zero_24_matrix := by
  dsimp only [zero_24_matrix,zero_24_cell_00,zero_24_cell_01,zero_24_cell_02,zero_24_cell_03,zero_24_cell_04,zero_24_cell_11,zero_24_cell_12,zero_24_cell_13,zero_24_cell_14,zero_24_cell_22,zero_24_cell_23,zero_24_cell_24,zero_24_cell_33,zero_24_cell_34,zero_24_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_24_matrix_posDef : zero_24_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_24_first_pos zero_24_delta_pos zero_24_schur_pos
    zero_24_minor_pos zero_24_det_pos
  intro i j
  rw [← zero_24_matrix_eq]
  exact smallCoefficient_symmetric 0 24 i j

private theorem zero_24_posDef : (smallCoefficient 0 24).PosDef := by
  rw [zero_24_matrix_eq]
  exact zero_24_matrix_posDef


private def zero_25_moment_0 : {v : ℝ // momentCoefficient 0 25 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_25_moment_1 : {v : ℝ // momentCoefficient 0 25 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_25_moment_2 : {v : ℝ // momentCoefficient 0 25 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_25_moment_3 : {v : ℝ // momentCoefficient 0 25 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_25_moment_4 : {v : ℝ // momentCoefficient 0 25 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_25_moment_5 : {v : ℝ // momentCoefficient 0 25 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_25_moment_6 : {v : ℝ // momentCoefficient 0 25 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_25_moment_7 : {v : ℝ // momentCoefficient 0 25 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_25_moment_8 : {v : ℝ // momentCoefficient 0 25 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def zero_25_cell_00 : {v : ℝ // smallCoefficient 0 25 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,zero_25_moment_0.property]
      dsimp only [zero_25_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_01 : {v : ℝ // smallCoefficient 0 25 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,zero_25_moment_0.property,zero_25_moment_1.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_02 : {v : ℝ // smallCoefficient 0 25 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_03 : {v : ℝ // smallCoefficient 0 25 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_04 : {v : ℝ // smallCoefficient 0 25 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property,zero_25_moment_4.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3,zero_25_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_11 : {v : ℝ // smallCoefficient 0 25 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_12 : {v : ℝ // smallCoefficient 0 25 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_13 : {v : ℝ // smallCoefficient 0 25 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property,zero_25_moment_4.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3,zero_25_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_14 : {v : ℝ // smallCoefficient 0 25 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property,zero_25_moment_4.property,zero_25_moment_5.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3,zero_25_moment_4,zero_25_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_22 : {v : ℝ // smallCoefficient 0 25 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property,zero_25_moment_4.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3,zero_25_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_23 : {v : ℝ // smallCoefficient 0 25 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property,zero_25_moment_4.property,zero_25_moment_5.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3,zero_25_moment_4,zero_25_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_24 : {v : ℝ // smallCoefficient 0 25 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property,zero_25_moment_4.property,zero_25_moment_5.property,zero_25_moment_6.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3,zero_25_moment_4,zero_25_moment_5,zero_25_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_33 : {v : ℝ // smallCoefficient 0 25 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property,zero_25_moment_4.property,zero_25_moment_5.property,zero_25_moment_6.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3,zero_25_moment_4,zero_25_moment_5,zero_25_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_34 : {v : ℝ // smallCoefficient 0 25 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property,zero_25_moment_4.property,zero_25_moment_5.property,zero_25_moment_6.property,zero_25_moment_7.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3,zero_25_moment_4,zero_25_moment_5,zero_25_moment_6,zero_25_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_cell_44 : {v : ℝ // smallCoefficient 0 25 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,zero_25_moment_0.property,zero_25_moment_1.property,zero_25_moment_2.property,zero_25_moment_3.property,zero_25_moment_4.property,zero_25_moment_5.property,zero_25_moment_6.property,zero_25_moment_7.property,zero_25_moment_8.property]
      dsimp only [zero_25_moment_0,zero_25_moment_1,zero_25_moment_2,zero_25_moment_3,zero_25_moment_4,zero_25_moment_5,zero_25_moment_6,zero_25_moment_7,zero_25_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def zero_25_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![zero_25_cell_00.val,zero_25_cell_01.val,zero_25_cell_02.val,zero_25_cell_03.val,zero_25_cell_04.val],
    ![zero_25_cell_01.val,zero_25_cell_11.val,zero_25_cell_12.val,zero_25_cell_13.val,zero_25_cell_14.val],
    ![zero_25_cell_02.val,zero_25_cell_12.val,zero_25_cell_22.val,zero_25_cell_23.val,zero_25_cell_24.val],
    ![zero_25_cell_03.val,zero_25_cell_13.val,zero_25_cell_23.val,zero_25_cell_33.val,zero_25_cell_34.val],
    ![zero_25_cell_04.val,zero_25_cell_14.val,zero_25_cell_24.val,zero_25_cell_34.val,zero_25_cell_44.val]]

private theorem zero_25_matrix_eq : smallCoefficient 0 25=zero_25_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact zero_25_cell_00.property
  · exact zero_25_cell_01.property
  · exact zero_25_cell_02.property
  · exact zero_25_cell_03.property
  · exact zero_25_cell_04.property
  · exact (smallCoefficient_symmetric 0 25 1 0).trans zero_25_cell_01.property
  · exact zero_25_cell_11.property
  · exact zero_25_cell_12.property
  · exact zero_25_cell_13.property
  · exact zero_25_cell_14.property
  · exact (smallCoefficient_symmetric 0 25 2 0).trans zero_25_cell_02.property
  · exact (smallCoefficient_symmetric 0 25 2 1).trans zero_25_cell_12.property
  · exact zero_25_cell_22.property
  · exact zero_25_cell_23.property
  · exact zero_25_cell_24.property
  · exact (smallCoefficient_symmetric 0 25 3 0).trans zero_25_cell_03.property
  · exact (smallCoefficient_symmetric 0 25 3 1).trans zero_25_cell_13.property
  · exact (smallCoefficient_symmetric 0 25 3 2).trans zero_25_cell_23.property
  · exact zero_25_cell_33.property
  · exact zero_25_cell_34.property
  · exact (smallCoefficient_symmetric 0 25 4 0).trans zero_25_cell_04.property
  · exact (smallCoefficient_symmetric 0 25 4 1).trans zero_25_cell_14.property
  · exact (smallCoefficient_symmetric 0 25 4 2).trans zero_25_cell_24.property
  · exact (smallCoefficient_symmetric 0 25 4 3).trans zero_25_cell_34.property
  · exact zero_25_cell_44.property

private theorem zero_25_first_pos : 0 < zero_25_matrix 0 0 := by
  dsimp only [zero_25_matrix,zero_25_cell_00,zero_25_cell_01,zero_25_cell_02,zero_25_cell_03,zero_25_cell_04,zero_25_cell_11,zero_25_cell_12,zero_25_cell_13,zero_25_cell_14,zero_25_cell_22,zero_25_cell_23,zero_25_cell_24,zero_25_cell_33,zero_25_cell_34,zero_25_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem zero_25_delta_pos : 0 < delta zero_25_matrix := by
  dsimp only [zero_25_matrix,zero_25_cell_00,zero_25_cell_01,zero_25_cell_02,zero_25_cell_03,zero_25_cell_04,zero_25_cell_11,zero_25_cell_12,zero_25_cell_13,zero_25_cell_14,zero_25_cell_22,zero_25_cell_23,zero_25_cell_24,zero_25_cell_33,zero_25_cell_34,zero_25_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem zero_25_schur_pos : 0 < schur zero_25_matrix 0 0 := by
  dsimp only [zero_25_matrix,zero_25_cell_00,zero_25_cell_01,zero_25_cell_02,zero_25_cell_03,zero_25_cell_04,zero_25_cell_11,zero_25_cell_12,zero_25_cell_13,zero_25_cell_14,zero_25_cell_22,zero_25_cell_23,zero_25_cell_24,zero_25_cell_33,zero_25_cell_34,zero_25_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem zero_25_minor_pos : 0 < minor zero_25_matrix := by
  dsimp only [zero_25_matrix,zero_25_cell_00,zero_25_cell_01,zero_25_cell_02,zero_25_cell_03,zero_25_cell_04,zero_25_cell_11,zero_25_cell_12,zero_25_cell_13,zero_25_cell_14,zero_25_cell_22,zero_25_cell_23,zero_25_cell_24,zero_25_cell_33,zero_25_cell_34,zero_25_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem zero_25_det_pos : 0 < determinant zero_25_matrix := by
  dsimp only [zero_25_matrix,zero_25_cell_00,zero_25_cell_01,zero_25_cell_02,zero_25_cell_03,zero_25_cell_04,zero_25_cell_11,zero_25_cell_12,zero_25_cell_13,zero_25_cell_14,zero_25_cell_22,zero_25_cell_23,zero_25_cell_24,zero_25_cell_33,zero_25_cell_34,zero_25_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem zero_25_matrix_posDef : zero_25_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ zero_25_first_pos zero_25_delta_pos zero_25_schur_pos
    zero_25_minor_pos zero_25_det_pos
  intro i j
  rw [← zero_25_matrix_eq]
  exact smallCoefficient_symmetric 0 25 i j

private theorem zero_25_posDef : (smallCoefficient 0 25).PosDef := by
  rw [zero_25_matrix_eq]
  exact zero_25_matrix_posDef


private def upper_0_moment_0 : {v : ℝ // momentCoefficient weightSeven 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_0_moment_1 : {v : ℝ // momentCoefficient weightSeven 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_0_moment_2 : {v : ℝ // momentCoefficient weightSeven 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_0_moment_3 : {v : ℝ // momentCoefficient weightSeven 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_0_moment_4 : {v : ℝ // momentCoefficient weightSeven 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_0_moment_5 : {v : ℝ // momentCoefficient weightSeven 0 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_0_moment_6 : {v : ℝ // momentCoefficient weightSeven 0 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_0_moment_7 : {v : ℝ // momentCoefficient weightSeven 0 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_0_moment_8 : {v : ℝ // momentCoefficient weightSeven 0 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_0_cell_00 : {v : ℝ // smallCoefficient weightSeven 0 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_0_moment_0.property]
      dsimp only [upper_0_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_01 : {v : ℝ // smallCoefficient weightSeven 0 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_0_moment_0.property,upper_0_moment_1.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_02 : {v : ℝ // smallCoefficient weightSeven 0 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_03 : {v : ℝ // smallCoefficient weightSeven 0 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_04 : {v : ℝ // smallCoefficient weightSeven 0 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property,upper_0_moment_4.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3,upper_0_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_11 : {v : ℝ // smallCoefficient weightSeven 0 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_12 : {v : ℝ // smallCoefficient weightSeven 0 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_13 : {v : ℝ // smallCoefficient weightSeven 0 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property,upper_0_moment_4.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3,upper_0_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_14 : {v : ℝ // smallCoefficient weightSeven 0 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property,upper_0_moment_4.property,upper_0_moment_5.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3,upper_0_moment_4,upper_0_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_22 : {v : ℝ // smallCoefficient weightSeven 0 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property,upper_0_moment_4.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3,upper_0_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_23 : {v : ℝ // smallCoefficient weightSeven 0 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property,upper_0_moment_4.property,upper_0_moment_5.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3,upper_0_moment_4,upper_0_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_24 : {v : ℝ // smallCoefficient weightSeven 0 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property,upper_0_moment_4.property,upper_0_moment_5.property,upper_0_moment_6.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3,upper_0_moment_4,upper_0_moment_5,upper_0_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_33 : {v : ℝ // smallCoefficient weightSeven 0 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property,upper_0_moment_4.property,upper_0_moment_5.property,upper_0_moment_6.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3,upper_0_moment_4,upper_0_moment_5,upper_0_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_34 : {v : ℝ // smallCoefficient weightSeven 0 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property,upper_0_moment_4.property,upper_0_moment_5.property,upper_0_moment_6.property,upper_0_moment_7.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3,upper_0_moment_4,upper_0_moment_5,upper_0_moment_6,upper_0_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_cell_44 : {v : ℝ // smallCoefficient weightSeven 0 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_0_moment_0.property,upper_0_moment_1.property,upper_0_moment_2.property,upper_0_moment_3.property,upper_0_moment_4.property,upper_0_moment_5.property,upper_0_moment_6.property,upper_0_moment_7.property,upper_0_moment_8.property]
      dsimp only [upper_0_moment_0,upper_0_moment_1,upper_0_moment_2,upper_0_moment_3,upper_0_moment_4,upper_0_moment_5,upper_0_moment_6,upper_0_moment_7,upper_0_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_0_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_0_cell_00.val,upper_0_cell_01.val,upper_0_cell_02.val,upper_0_cell_03.val,upper_0_cell_04.val],
    ![upper_0_cell_01.val,upper_0_cell_11.val,upper_0_cell_12.val,upper_0_cell_13.val,upper_0_cell_14.val],
    ![upper_0_cell_02.val,upper_0_cell_12.val,upper_0_cell_22.val,upper_0_cell_23.val,upper_0_cell_24.val],
    ![upper_0_cell_03.val,upper_0_cell_13.val,upper_0_cell_23.val,upper_0_cell_33.val,upper_0_cell_34.val],
    ![upper_0_cell_04.val,upper_0_cell_14.val,upper_0_cell_24.val,upper_0_cell_34.val,upper_0_cell_44.val]]

private theorem upper_0_matrix_eq : smallCoefficient weightSeven 0=upper_0_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_0_cell_00.property
  · exact upper_0_cell_01.property
  · exact upper_0_cell_02.property
  · exact upper_0_cell_03.property
  · exact upper_0_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 0 1 0).trans upper_0_cell_01.property
  · exact upper_0_cell_11.property
  · exact upper_0_cell_12.property
  · exact upper_0_cell_13.property
  · exact upper_0_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 0 2 0).trans upper_0_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 0 2 1).trans upper_0_cell_12.property
  · exact upper_0_cell_22.property
  · exact upper_0_cell_23.property
  · exact upper_0_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 0 3 0).trans upper_0_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 0 3 1).trans upper_0_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 0 3 2).trans upper_0_cell_23.property
  · exact upper_0_cell_33.property
  · exact upper_0_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 0 4 0).trans upper_0_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 0 4 1).trans upper_0_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 0 4 2).trans upper_0_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 0 4 3).trans upper_0_cell_34.property
  · exact upper_0_cell_44.property

private theorem upper_0_first_pos : 0 < upper_0_matrix 0 0 := by
  dsimp only [upper_0_matrix,upper_0_cell_00,upper_0_cell_01,upper_0_cell_02,upper_0_cell_03,upper_0_cell_04,upper_0_cell_11,upper_0_cell_12,upper_0_cell_13,upper_0_cell_14,upper_0_cell_22,upper_0_cell_23,upper_0_cell_24,upper_0_cell_33,upper_0_cell_34,upper_0_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_0_delta_pos : 0 < delta upper_0_matrix := by
  dsimp only [upper_0_matrix,upper_0_cell_00,upper_0_cell_01,upper_0_cell_02,upper_0_cell_03,upper_0_cell_04,upper_0_cell_11,upper_0_cell_12,upper_0_cell_13,upper_0_cell_14,upper_0_cell_22,upper_0_cell_23,upper_0_cell_24,upper_0_cell_33,upper_0_cell_34,upper_0_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_0_schur_pos : 0 < schur upper_0_matrix 0 0 := by
  dsimp only [upper_0_matrix,upper_0_cell_00,upper_0_cell_01,upper_0_cell_02,upper_0_cell_03,upper_0_cell_04,upper_0_cell_11,upper_0_cell_12,upper_0_cell_13,upper_0_cell_14,upper_0_cell_22,upper_0_cell_23,upper_0_cell_24,upper_0_cell_33,upper_0_cell_34,upper_0_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_0_minor_pos : 0 < minor upper_0_matrix := by
  dsimp only [upper_0_matrix,upper_0_cell_00,upper_0_cell_01,upper_0_cell_02,upper_0_cell_03,upper_0_cell_04,upper_0_cell_11,upper_0_cell_12,upper_0_cell_13,upper_0_cell_14,upper_0_cell_22,upper_0_cell_23,upper_0_cell_24,upper_0_cell_33,upper_0_cell_34,upper_0_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_0_det_pos : 0 < determinant upper_0_matrix := by
  dsimp only [upper_0_matrix,upper_0_cell_00,upper_0_cell_01,upper_0_cell_02,upper_0_cell_03,upper_0_cell_04,upper_0_cell_11,upper_0_cell_12,upper_0_cell_13,upper_0_cell_14,upper_0_cell_22,upper_0_cell_23,upper_0_cell_24,upper_0_cell_33,upper_0_cell_34,upper_0_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_0_matrix_posDef : upper_0_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_0_first_pos upper_0_delta_pos upper_0_schur_pos
    upper_0_minor_pos upper_0_det_pos
  intro i j
  rw [← upper_0_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 0 i j

private theorem upper_0_posDef : (smallCoefficient weightSeven 0).PosDef := by
  rw [upper_0_matrix_eq]
  exact upper_0_matrix_posDef


private def upper_1_moment_0 : {v : ℝ // momentCoefficient weightSeven 1 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_1_moment_1 : {v : ℝ // momentCoefficient weightSeven 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_1_moment_2 : {v : ℝ // momentCoefficient weightSeven 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_1_moment_3 : {v : ℝ // momentCoefficient weightSeven 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_1_moment_4 : {v : ℝ // momentCoefficient weightSeven 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_1_moment_5 : {v : ℝ // momentCoefficient weightSeven 1 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_1_moment_6 : {v : ℝ // momentCoefficient weightSeven 1 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_1_moment_7 : {v : ℝ // momentCoefficient weightSeven 1 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_1_moment_8 : {v : ℝ // momentCoefficient weightSeven 1 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_1_cell_00 : {v : ℝ // smallCoefficient weightSeven 1 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_1_moment_0.property]
      dsimp only [upper_1_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_01 : {v : ℝ // smallCoefficient weightSeven 1 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_1_moment_0.property,upper_1_moment_1.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_02 : {v : ℝ // smallCoefficient weightSeven 1 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_03 : {v : ℝ // smallCoefficient weightSeven 1 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_04 : {v : ℝ // smallCoefficient weightSeven 1 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property,upper_1_moment_4.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3,upper_1_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_11 : {v : ℝ // smallCoefficient weightSeven 1 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_12 : {v : ℝ // smallCoefficient weightSeven 1 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_13 : {v : ℝ // smallCoefficient weightSeven 1 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property,upper_1_moment_4.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3,upper_1_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_14 : {v : ℝ // smallCoefficient weightSeven 1 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property,upper_1_moment_4.property,upper_1_moment_5.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3,upper_1_moment_4,upper_1_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_22 : {v : ℝ // smallCoefficient weightSeven 1 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property,upper_1_moment_4.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3,upper_1_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_23 : {v : ℝ // smallCoefficient weightSeven 1 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property,upper_1_moment_4.property,upper_1_moment_5.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3,upper_1_moment_4,upper_1_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_24 : {v : ℝ // smallCoefficient weightSeven 1 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property,upper_1_moment_4.property,upper_1_moment_5.property,upper_1_moment_6.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3,upper_1_moment_4,upper_1_moment_5,upper_1_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_33 : {v : ℝ // smallCoefficient weightSeven 1 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property,upper_1_moment_4.property,upper_1_moment_5.property,upper_1_moment_6.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3,upper_1_moment_4,upper_1_moment_5,upper_1_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_34 : {v : ℝ // smallCoefficient weightSeven 1 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property,upper_1_moment_4.property,upper_1_moment_5.property,upper_1_moment_6.property,upper_1_moment_7.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3,upper_1_moment_4,upper_1_moment_5,upper_1_moment_6,upper_1_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_cell_44 : {v : ℝ // smallCoefficient weightSeven 1 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_1_moment_0.property,upper_1_moment_1.property,upper_1_moment_2.property,upper_1_moment_3.property,upper_1_moment_4.property,upper_1_moment_5.property,upper_1_moment_6.property,upper_1_moment_7.property,upper_1_moment_8.property]
      dsimp only [upper_1_moment_0,upper_1_moment_1,upper_1_moment_2,upper_1_moment_3,upper_1_moment_4,upper_1_moment_5,upper_1_moment_6,upper_1_moment_7,upper_1_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_1_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_1_cell_00.val,upper_1_cell_01.val,upper_1_cell_02.val,upper_1_cell_03.val,upper_1_cell_04.val],
    ![upper_1_cell_01.val,upper_1_cell_11.val,upper_1_cell_12.val,upper_1_cell_13.val,upper_1_cell_14.val],
    ![upper_1_cell_02.val,upper_1_cell_12.val,upper_1_cell_22.val,upper_1_cell_23.val,upper_1_cell_24.val],
    ![upper_1_cell_03.val,upper_1_cell_13.val,upper_1_cell_23.val,upper_1_cell_33.val,upper_1_cell_34.val],
    ![upper_1_cell_04.val,upper_1_cell_14.val,upper_1_cell_24.val,upper_1_cell_34.val,upper_1_cell_44.val]]

private theorem upper_1_matrix_eq : smallCoefficient weightSeven 1=upper_1_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_1_cell_00.property
  · exact upper_1_cell_01.property
  · exact upper_1_cell_02.property
  · exact upper_1_cell_03.property
  · exact upper_1_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 1 1 0).trans upper_1_cell_01.property
  · exact upper_1_cell_11.property
  · exact upper_1_cell_12.property
  · exact upper_1_cell_13.property
  · exact upper_1_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 1 2 0).trans upper_1_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 1 2 1).trans upper_1_cell_12.property
  · exact upper_1_cell_22.property
  · exact upper_1_cell_23.property
  · exact upper_1_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 1 3 0).trans upper_1_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 1 3 1).trans upper_1_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 1 3 2).trans upper_1_cell_23.property
  · exact upper_1_cell_33.property
  · exact upper_1_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 1 4 0).trans upper_1_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 1 4 1).trans upper_1_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 1 4 2).trans upper_1_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 1 4 3).trans upper_1_cell_34.property
  · exact upper_1_cell_44.property

private theorem upper_1_first_pos : 0 < upper_1_matrix 0 0 := by
  dsimp only [upper_1_matrix,upper_1_cell_00,upper_1_cell_01,upper_1_cell_02,upper_1_cell_03,upper_1_cell_04,upper_1_cell_11,upper_1_cell_12,upper_1_cell_13,upper_1_cell_14,upper_1_cell_22,upper_1_cell_23,upper_1_cell_24,upper_1_cell_33,upper_1_cell_34,upper_1_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_1_delta_pos : 0 < delta upper_1_matrix := by
  dsimp only [upper_1_matrix,upper_1_cell_00,upper_1_cell_01,upper_1_cell_02,upper_1_cell_03,upper_1_cell_04,upper_1_cell_11,upper_1_cell_12,upper_1_cell_13,upper_1_cell_14,upper_1_cell_22,upper_1_cell_23,upper_1_cell_24,upper_1_cell_33,upper_1_cell_34,upper_1_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_1_schur_pos : 0 < schur upper_1_matrix 0 0 := by
  dsimp only [upper_1_matrix,upper_1_cell_00,upper_1_cell_01,upper_1_cell_02,upper_1_cell_03,upper_1_cell_04,upper_1_cell_11,upper_1_cell_12,upper_1_cell_13,upper_1_cell_14,upper_1_cell_22,upper_1_cell_23,upper_1_cell_24,upper_1_cell_33,upper_1_cell_34,upper_1_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_1_minor_pos : 0 < minor upper_1_matrix := by
  dsimp only [upper_1_matrix,upper_1_cell_00,upper_1_cell_01,upper_1_cell_02,upper_1_cell_03,upper_1_cell_04,upper_1_cell_11,upper_1_cell_12,upper_1_cell_13,upper_1_cell_14,upper_1_cell_22,upper_1_cell_23,upper_1_cell_24,upper_1_cell_33,upper_1_cell_34,upper_1_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_1_det_pos : 0 < determinant upper_1_matrix := by
  dsimp only [upper_1_matrix,upper_1_cell_00,upper_1_cell_01,upper_1_cell_02,upper_1_cell_03,upper_1_cell_04,upper_1_cell_11,upper_1_cell_12,upper_1_cell_13,upper_1_cell_14,upper_1_cell_22,upper_1_cell_23,upper_1_cell_24,upper_1_cell_33,upper_1_cell_34,upper_1_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_1_matrix_posDef : upper_1_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_1_first_pos upper_1_delta_pos upper_1_schur_pos
    upper_1_minor_pos upper_1_det_pos
  intro i j
  rw [← upper_1_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 1 i j

private theorem upper_1_posDef : (smallCoefficient weightSeven 1).PosDef := by
  rw [upper_1_matrix_eq]
  exact upper_1_matrix_posDef


private def upper_2_moment_0 : {v : ℝ // momentCoefficient weightSeven 2 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_2_moment_1 : {v : ℝ // momentCoefficient weightSeven 2 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_2_moment_2 : {v : ℝ // momentCoefficient weightSeven 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_2_moment_3 : {v : ℝ // momentCoefficient weightSeven 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_2_moment_4 : {v : ℝ // momentCoefficient weightSeven 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_2_moment_5 : {v : ℝ // momentCoefficient weightSeven 2 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_2_moment_6 : {v : ℝ // momentCoefficient weightSeven 2 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_2_moment_7 : {v : ℝ // momentCoefficient weightSeven 2 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_2_moment_8 : {v : ℝ // momentCoefficient weightSeven 2 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_2_cell_00 : {v : ℝ // smallCoefficient weightSeven 2 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_2_moment_0.property]
      dsimp only [upper_2_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_01 : {v : ℝ // smallCoefficient weightSeven 2 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_2_moment_0.property,upper_2_moment_1.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_02 : {v : ℝ // smallCoefficient weightSeven 2 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_03 : {v : ℝ // smallCoefficient weightSeven 2 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_04 : {v : ℝ // smallCoefficient weightSeven 2 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property,upper_2_moment_4.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3,upper_2_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_11 : {v : ℝ // smallCoefficient weightSeven 2 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_12 : {v : ℝ // smallCoefficient weightSeven 2 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_13 : {v : ℝ // smallCoefficient weightSeven 2 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property,upper_2_moment_4.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3,upper_2_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_14 : {v : ℝ // smallCoefficient weightSeven 2 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property,upper_2_moment_4.property,upper_2_moment_5.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3,upper_2_moment_4,upper_2_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_22 : {v : ℝ // smallCoefficient weightSeven 2 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property,upper_2_moment_4.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3,upper_2_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_23 : {v : ℝ // smallCoefficient weightSeven 2 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property,upper_2_moment_4.property,upper_2_moment_5.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3,upper_2_moment_4,upper_2_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_24 : {v : ℝ // smallCoefficient weightSeven 2 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property,upper_2_moment_4.property,upper_2_moment_5.property,upper_2_moment_6.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3,upper_2_moment_4,upper_2_moment_5,upper_2_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_33 : {v : ℝ // smallCoefficient weightSeven 2 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property,upper_2_moment_4.property,upper_2_moment_5.property,upper_2_moment_6.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3,upper_2_moment_4,upper_2_moment_5,upper_2_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_34 : {v : ℝ // smallCoefficient weightSeven 2 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property,upper_2_moment_4.property,upper_2_moment_5.property,upper_2_moment_6.property,upper_2_moment_7.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3,upper_2_moment_4,upper_2_moment_5,upper_2_moment_6,upper_2_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_cell_44 : {v : ℝ // smallCoefficient weightSeven 2 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_2_moment_0.property,upper_2_moment_1.property,upper_2_moment_2.property,upper_2_moment_3.property,upper_2_moment_4.property,upper_2_moment_5.property,upper_2_moment_6.property,upper_2_moment_7.property,upper_2_moment_8.property]
      dsimp only [upper_2_moment_0,upper_2_moment_1,upper_2_moment_2,upper_2_moment_3,upper_2_moment_4,upper_2_moment_5,upper_2_moment_6,upper_2_moment_7,upper_2_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_2_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_2_cell_00.val,upper_2_cell_01.val,upper_2_cell_02.val,upper_2_cell_03.val,upper_2_cell_04.val],
    ![upper_2_cell_01.val,upper_2_cell_11.val,upper_2_cell_12.val,upper_2_cell_13.val,upper_2_cell_14.val],
    ![upper_2_cell_02.val,upper_2_cell_12.val,upper_2_cell_22.val,upper_2_cell_23.val,upper_2_cell_24.val],
    ![upper_2_cell_03.val,upper_2_cell_13.val,upper_2_cell_23.val,upper_2_cell_33.val,upper_2_cell_34.val],
    ![upper_2_cell_04.val,upper_2_cell_14.val,upper_2_cell_24.val,upper_2_cell_34.val,upper_2_cell_44.val]]

private theorem upper_2_matrix_eq : smallCoefficient weightSeven 2=upper_2_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_2_cell_00.property
  · exact upper_2_cell_01.property
  · exact upper_2_cell_02.property
  · exact upper_2_cell_03.property
  · exact upper_2_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 2 1 0).trans upper_2_cell_01.property
  · exact upper_2_cell_11.property
  · exact upper_2_cell_12.property
  · exact upper_2_cell_13.property
  · exact upper_2_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 2 2 0).trans upper_2_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 2 2 1).trans upper_2_cell_12.property
  · exact upper_2_cell_22.property
  · exact upper_2_cell_23.property
  · exact upper_2_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 2 3 0).trans upper_2_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 2 3 1).trans upper_2_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 2 3 2).trans upper_2_cell_23.property
  · exact upper_2_cell_33.property
  · exact upper_2_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 2 4 0).trans upper_2_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 2 4 1).trans upper_2_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 2 4 2).trans upper_2_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 2 4 3).trans upper_2_cell_34.property
  · exact upper_2_cell_44.property

private theorem upper_2_first_pos : 0 < upper_2_matrix 0 0 := by
  dsimp only [upper_2_matrix,upper_2_cell_00,upper_2_cell_01,upper_2_cell_02,upper_2_cell_03,upper_2_cell_04,upper_2_cell_11,upper_2_cell_12,upper_2_cell_13,upper_2_cell_14,upper_2_cell_22,upper_2_cell_23,upper_2_cell_24,upper_2_cell_33,upper_2_cell_34,upper_2_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_2_delta_pos : 0 < delta upper_2_matrix := by
  dsimp only [upper_2_matrix,upper_2_cell_00,upper_2_cell_01,upper_2_cell_02,upper_2_cell_03,upper_2_cell_04,upper_2_cell_11,upper_2_cell_12,upper_2_cell_13,upper_2_cell_14,upper_2_cell_22,upper_2_cell_23,upper_2_cell_24,upper_2_cell_33,upper_2_cell_34,upper_2_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_2_schur_pos : 0 < schur upper_2_matrix 0 0 := by
  dsimp only [upper_2_matrix,upper_2_cell_00,upper_2_cell_01,upper_2_cell_02,upper_2_cell_03,upper_2_cell_04,upper_2_cell_11,upper_2_cell_12,upper_2_cell_13,upper_2_cell_14,upper_2_cell_22,upper_2_cell_23,upper_2_cell_24,upper_2_cell_33,upper_2_cell_34,upper_2_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_2_minor_pos : 0 < minor upper_2_matrix := by
  dsimp only [upper_2_matrix,upper_2_cell_00,upper_2_cell_01,upper_2_cell_02,upper_2_cell_03,upper_2_cell_04,upper_2_cell_11,upper_2_cell_12,upper_2_cell_13,upper_2_cell_14,upper_2_cell_22,upper_2_cell_23,upper_2_cell_24,upper_2_cell_33,upper_2_cell_34,upper_2_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_2_det_pos : 0 < determinant upper_2_matrix := by
  dsimp only [upper_2_matrix,upper_2_cell_00,upper_2_cell_01,upper_2_cell_02,upper_2_cell_03,upper_2_cell_04,upper_2_cell_11,upper_2_cell_12,upper_2_cell_13,upper_2_cell_14,upper_2_cell_22,upper_2_cell_23,upper_2_cell_24,upper_2_cell_33,upper_2_cell_34,upper_2_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_2_matrix_posDef : upper_2_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_2_first_pos upper_2_delta_pos upper_2_schur_pos
    upper_2_minor_pos upper_2_det_pos
  intro i j
  rw [← upper_2_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 2 i j

private theorem upper_2_posDef : (smallCoefficient weightSeven 2).PosDef := by
  rw [upper_2_matrix_eq]
  exact upper_2_matrix_posDef


private def upper_3_moment_0 : {v : ℝ // momentCoefficient weightSeven 3 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_3_moment_1 : {v : ℝ // momentCoefficient weightSeven 3 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_3_moment_2 : {v : ℝ // momentCoefficient weightSeven 3 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_3_moment_3 : {v : ℝ // momentCoefficient weightSeven 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_3_moment_4 : {v : ℝ // momentCoefficient weightSeven 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_3_moment_5 : {v : ℝ // momentCoefficient weightSeven 3 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_3_moment_6 : {v : ℝ // momentCoefficient weightSeven 3 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_3_moment_7 : {v : ℝ // momentCoefficient weightSeven 3 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_3_moment_8 : {v : ℝ // momentCoefficient weightSeven 3 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_3_cell_00 : {v : ℝ // smallCoefficient weightSeven 3 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_3_moment_0.property]
      dsimp only [upper_3_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_01 : {v : ℝ // smallCoefficient weightSeven 3 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_3_moment_0.property,upper_3_moment_1.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_02 : {v : ℝ // smallCoefficient weightSeven 3 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_03 : {v : ℝ // smallCoefficient weightSeven 3 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_04 : {v : ℝ // smallCoefficient weightSeven 3 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property,upper_3_moment_4.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3,upper_3_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_11 : {v : ℝ // smallCoefficient weightSeven 3 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_12 : {v : ℝ // smallCoefficient weightSeven 3 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_13 : {v : ℝ // smallCoefficient weightSeven 3 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property,upper_3_moment_4.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3,upper_3_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_14 : {v : ℝ // smallCoefficient weightSeven 3 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property,upper_3_moment_4.property,upper_3_moment_5.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3,upper_3_moment_4,upper_3_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_22 : {v : ℝ // smallCoefficient weightSeven 3 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property,upper_3_moment_4.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3,upper_3_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_23 : {v : ℝ // smallCoefficient weightSeven 3 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property,upper_3_moment_4.property,upper_3_moment_5.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3,upper_3_moment_4,upper_3_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_24 : {v : ℝ // smallCoefficient weightSeven 3 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property,upper_3_moment_4.property,upper_3_moment_5.property,upper_3_moment_6.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3,upper_3_moment_4,upper_3_moment_5,upper_3_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_33 : {v : ℝ // smallCoefficient weightSeven 3 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property,upper_3_moment_4.property,upper_3_moment_5.property,upper_3_moment_6.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3,upper_3_moment_4,upper_3_moment_5,upper_3_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_34 : {v : ℝ // smallCoefficient weightSeven 3 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property,upper_3_moment_4.property,upper_3_moment_5.property,upper_3_moment_6.property,upper_3_moment_7.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3,upper_3_moment_4,upper_3_moment_5,upper_3_moment_6,upper_3_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_cell_44 : {v : ℝ // smallCoefficient weightSeven 3 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_3_moment_0.property,upper_3_moment_1.property,upper_3_moment_2.property,upper_3_moment_3.property,upper_3_moment_4.property,upper_3_moment_5.property,upper_3_moment_6.property,upper_3_moment_7.property,upper_3_moment_8.property]
      dsimp only [upper_3_moment_0,upper_3_moment_1,upper_3_moment_2,upper_3_moment_3,upper_3_moment_4,upper_3_moment_5,upper_3_moment_6,upper_3_moment_7,upper_3_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_3_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_3_cell_00.val,upper_3_cell_01.val,upper_3_cell_02.val,upper_3_cell_03.val,upper_3_cell_04.val],
    ![upper_3_cell_01.val,upper_3_cell_11.val,upper_3_cell_12.val,upper_3_cell_13.val,upper_3_cell_14.val],
    ![upper_3_cell_02.val,upper_3_cell_12.val,upper_3_cell_22.val,upper_3_cell_23.val,upper_3_cell_24.val],
    ![upper_3_cell_03.val,upper_3_cell_13.val,upper_3_cell_23.val,upper_3_cell_33.val,upper_3_cell_34.val],
    ![upper_3_cell_04.val,upper_3_cell_14.val,upper_3_cell_24.val,upper_3_cell_34.val,upper_3_cell_44.val]]

private theorem upper_3_matrix_eq : smallCoefficient weightSeven 3=upper_3_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_3_cell_00.property
  · exact upper_3_cell_01.property
  · exact upper_3_cell_02.property
  · exact upper_3_cell_03.property
  · exact upper_3_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 3 1 0).trans upper_3_cell_01.property
  · exact upper_3_cell_11.property
  · exact upper_3_cell_12.property
  · exact upper_3_cell_13.property
  · exact upper_3_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 3 2 0).trans upper_3_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 3 2 1).trans upper_3_cell_12.property
  · exact upper_3_cell_22.property
  · exact upper_3_cell_23.property
  · exact upper_3_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 3 3 0).trans upper_3_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 3 3 1).trans upper_3_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 3 3 2).trans upper_3_cell_23.property
  · exact upper_3_cell_33.property
  · exact upper_3_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 3 4 0).trans upper_3_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 3 4 1).trans upper_3_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 3 4 2).trans upper_3_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 3 4 3).trans upper_3_cell_34.property
  · exact upper_3_cell_44.property

private theorem upper_3_first_pos : 0 < upper_3_matrix 0 0 := by
  dsimp only [upper_3_matrix,upper_3_cell_00,upper_3_cell_01,upper_3_cell_02,upper_3_cell_03,upper_3_cell_04,upper_3_cell_11,upper_3_cell_12,upper_3_cell_13,upper_3_cell_14,upper_3_cell_22,upper_3_cell_23,upper_3_cell_24,upper_3_cell_33,upper_3_cell_34,upper_3_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_3_delta_pos : 0 < delta upper_3_matrix := by
  dsimp only [upper_3_matrix,upper_3_cell_00,upper_3_cell_01,upper_3_cell_02,upper_3_cell_03,upper_3_cell_04,upper_3_cell_11,upper_3_cell_12,upper_3_cell_13,upper_3_cell_14,upper_3_cell_22,upper_3_cell_23,upper_3_cell_24,upper_3_cell_33,upper_3_cell_34,upper_3_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_3_schur_pos : 0 < schur upper_3_matrix 0 0 := by
  dsimp only [upper_3_matrix,upper_3_cell_00,upper_3_cell_01,upper_3_cell_02,upper_3_cell_03,upper_3_cell_04,upper_3_cell_11,upper_3_cell_12,upper_3_cell_13,upper_3_cell_14,upper_3_cell_22,upper_3_cell_23,upper_3_cell_24,upper_3_cell_33,upper_3_cell_34,upper_3_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_3_minor_pos : 0 < minor upper_3_matrix := by
  dsimp only [upper_3_matrix,upper_3_cell_00,upper_3_cell_01,upper_3_cell_02,upper_3_cell_03,upper_3_cell_04,upper_3_cell_11,upper_3_cell_12,upper_3_cell_13,upper_3_cell_14,upper_3_cell_22,upper_3_cell_23,upper_3_cell_24,upper_3_cell_33,upper_3_cell_34,upper_3_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_3_det_pos : 0 < determinant upper_3_matrix := by
  dsimp only [upper_3_matrix,upper_3_cell_00,upper_3_cell_01,upper_3_cell_02,upper_3_cell_03,upper_3_cell_04,upper_3_cell_11,upper_3_cell_12,upper_3_cell_13,upper_3_cell_14,upper_3_cell_22,upper_3_cell_23,upper_3_cell_24,upper_3_cell_33,upper_3_cell_34,upper_3_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_3_matrix_posDef : upper_3_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_3_first_pos upper_3_delta_pos upper_3_schur_pos
    upper_3_minor_pos upper_3_det_pos
  intro i j
  rw [← upper_3_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 3 i j

private theorem upper_3_posDef : (smallCoefficient weightSeven 3).PosDef := by
  rw [upper_3_matrix_eq]
  exact upper_3_matrix_posDef


private def upper_4_moment_0 : {v : ℝ // momentCoefficient weightSeven 4 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_4_moment_1 : {v : ℝ // momentCoefficient weightSeven 4 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_4_moment_2 : {v : ℝ // momentCoefficient weightSeven 4 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_4_moment_3 : {v : ℝ // momentCoefficient weightSeven 4 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_4_moment_4 : {v : ℝ // momentCoefficient weightSeven 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_4_moment_5 : {v : ℝ // momentCoefficient weightSeven 4 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_4_moment_6 : {v : ℝ // momentCoefficient weightSeven 4 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_4_moment_7 : {v : ℝ // momentCoefficient weightSeven 4 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_4_moment_8 : {v : ℝ // momentCoefficient weightSeven 4 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_4_cell_00 : {v : ℝ // smallCoefficient weightSeven 4 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_4_moment_0.property]
      dsimp only [upper_4_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_01 : {v : ℝ // smallCoefficient weightSeven 4 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_4_moment_0.property,upper_4_moment_1.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_02 : {v : ℝ // smallCoefficient weightSeven 4 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_03 : {v : ℝ // smallCoefficient weightSeven 4 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_04 : {v : ℝ // smallCoefficient weightSeven 4 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property,upper_4_moment_4.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3,upper_4_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_11 : {v : ℝ // smallCoefficient weightSeven 4 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_12 : {v : ℝ // smallCoefficient weightSeven 4 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_13 : {v : ℝ // smallCoefficient weightSeven 4 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property,upper_4_moment_4.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3,upper_4_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_14 : {v : ℝ // smallCoefficient weightSeven 4 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property,upper_4_moment_4.property,upper_4_moment_5.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3,upper_4_moment_4,upper_4_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_22 : {v : ℝ // smallCoefficient weightSeven 4 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property,upper_4_moment_4.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3,upper_4_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_23 : {v : ℝ // smallCoefficient weightSeven 4 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property,upper_4_moment_4.property,upper_4_moment_5.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3,upper_4_moment_4,upper_4_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_24 : {v : ℝ // smallCoefficient weightSeven 4 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property,upper_4_moment_4.property,upper_4_moment_5.property,upper_4_moment_6.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3,upper_4_moment_4,upper_4_moment_5,upper_4_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_33 : {v : ℝ // smallCoefficient weightSeven 4 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property,upper_4_moment_4.property,upper_4_moment_5.property,upper_4_moment_6.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3,upper_4_moment_4,upper_4_moment_5,upper_4_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_34 : {v : ℝ // smallCoefficient weightSeven 4 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property,upper_4_moment_4.property,upper_4_moment_5.property,upper_4_moment_6.property,upper_4_moment_7.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3,upper_4_moment_4,upper_4_moment_5,upper_4_moment_6,upper_4_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_cell_44 : {v : ℝ // smallCoefficient weightSeven 4 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_4_moment_0.property,upper_4_moment_1.property,upper_4_moment_2.property,upper_4_moment_3.property,upper_4_moment_4.property,upper_4_moment_5.property,upper_4_moment_6.property,upper_4_moment_7.property,upper_4_moment_8.property]
      dsimp only [upper_4_moment_0,upper_4_moment_1,upper_4_moment_2,upper_4_moment_3,upper_4_moment_4,upper_4_moment_5,upper_4_moment_6,upper_4_moment_7,upper_4_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_4_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_4_cell_00.val,upper_4_cell_01.val,upper_4_cell_02.val,upper_4_cell_03.val,upper_4_cell_04.val],
    ![upper_4_cell_01.val,upper_4_cell_11.val,upper_4_cell_12.val,upper_4_cell_13.val,upper_4_cell_14.val],
    ![upper_4_cell_02.val,upper_4_cell_12.val,upper_4_cell_22.val,upper_4_cell_23.val,upper_4_cell_24.val],
    ![upper_4_cell_03.val,upper_4_cell_13.val,upper_4_cell_23.val,upper_4_cell_33.val,upper_4_cell_34.val],
    ![upper_4_cell_04.val,upper_4_cell_14.val,upper_4_cell_24.val,upper_4_cell_34.val,upper_4_cell_44.val]]

private theorem upper_4_matrix_eq : smallCoefficient weightSeven 4=upper_4_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_4_cell_00.property
  · exact upper_4_cell_01.property
  · exact upper_4_cell_02.property
  · exact upper_4_cell_03.property
  · exact upper_4_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 4 1 0).trans upper_4_cell_01.property
  · exact upper_4_cell_11.property
  · exact upper_4_cell_12.property
  · exact upper_4_cell_13.property
  · exact upper_4_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 4 2 0).trans upper_4_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 4 2 1).trans upper_4_cell_12.property
  · exact upper_4_cell_22.property
  · exact upper_4_cell_23.property
  · exact upper_4_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 4 3 0).trans upper_4_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 4 3 1).trans upper_4_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 4 3 2).trans upper_4_cell_23.property
  · exact upper_4_cell_33.property
  · exact upper_4_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 4 4 0).trans upper_4_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 4 4 1).trans upper_4_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 4 4 2).trans upper_4_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 4 4 3).trans upper_4_cell_34.property
  · exact upper_4_cell_44.property

private theorem upper_4_first_pos : 0 < upper_4_matrix 0 0 := by
  dsimp only [upper_4_matrix,upper_4_cell_00,upper_4_cell_01,upper_4_cell_02,upper_4_cell_03,upper_4_cell_04,upper_4_cell_11,upper_4_cell_12,upper_4_cell_13,upper_4_cell_14,upper_4_cell_22,upper_4_cell_23,upper_4_cell_24,upper_4_cell_33,upper_4_cell_34,upper_4_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_4_delta_pos : 0 < delta upper_4_matrix := by
  dsimp only [upper_4_matrix,upper_4_cell_00,upper_4_cell_01,upper_4_cell_02,upper_4_cell_03,upper_4_cell_04,upper_4_cell_11,upper_4_cell_12,upper_4_cell_13,upper_4_cell_14,upper_4_cell_22,upper_4_cell_23,upper_4_cell_24,upper_4_cell_33,upper_4_cell_34,upper_4_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_4_schur_pos : 0 < schur upper_4_matrix 0 0 := by
  dsimp only [upper_4_matrix,upper_4_cell_00,upper_4_cell_01,upper_4_cell_02,upper_4_cell_03,upper_4_cell_04,upper_4_cell_11,upper_4_cell_12,upper_4_cell_13,upper_4_cell_14,upper_4_cell_22,upper_4_cell_23,upper_4_cell_24,upper_4_cell_33,upper_4_cell_34,upper_4_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_4_minor_pos : 0 < minor upper_4_matrix := by
  dsimp only [upper_4_matrix,upper_4_cell_00,upper_4_cell_01,upper_4_cell_02,upper_4_cell_03,upper_4_cell_04,upper_4_cell_11,upper_4_cell_12,upper_4_cell_13,upper_4_cell_14,upper_4_cell_22,upper_4_cell_23,upper_4_cell_24,upper_4_cell_33,upper_4_cell_34,upper_4_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_4_det_pos : 0 < determinant upper_4_matrix := by
  dsimp only [upper_4_matrix,upper_4_cell_00,upper_4_cell_01,upper_4_cell_02,upper_4_cell_03,upper_4_cell_04,upper_4_cell_11,upper_4_cell_12,upper_4_cell_13,upper_4_cell_14,upper_4_cell_22,upper_4_cell_23,upper_4_cell_24,upper_4_cell_33,upper_4_cell_34,upper_4_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_4_matrix_posDef : upper_4_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_4_first_pos upper_4_delta_pos upper_4_schur_pos
    upper_4_minor_pos upper_4_det_pos
  intro i j
  rw [← upper_4_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 4 i j

private theorem upper_4_posDef : (smallCoefficient weightSeven 4).PosDef := by
  rw [upper_4_matrix_eq]
  exact upper_4_matrix_posDef


private def upper_5_moment_0 : {v : ℝ // momentCoefficient weightSeven 5 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_5_moment_1 : {v : ℝ // momentCoefficient weightSeven 5 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_5_moment_2 : {v : ℝ // momentCoefficient weightSeven 5 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_5_moment_3 : {v : ℝ // momentCoefficient weightSeven 5 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_5_moment_4 : {v : ℝ // momentCoefficient weightSeven 5 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_5_moment_5 : {v : ℝ // momentCoefficient weightSeven 5 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_5_moment_6 : {v : ℝ // momentCoefficient weightSeven 5 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_5_moment_7 : {v : ℝ // momentCoefficient weightSeven 5 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_5_moment_8 : {v : ℝ // momentCoefficient weightSeven 5 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_5_cell_00 : {v : ℝ // smallCoefficient weightSeven 5 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_5_moment_0.property]
      dsimp only [upper_5_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_01 : {v : ℝ // smallCoefficient weightSeven 5 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_5_moment_0.property,upper_5_moment_1.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_02 : {v : ℝ // smallCoefficient weightSeven 5 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_03 : {v : ℝ // smallCoefficient weightSeven 5 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_04 : {v : ℝ // smallCoefficient weightSeven 5 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property,upper_5_moment_4.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3,upper_5_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_11 : {v : ℝ // smallCoefficient weightSeven 5 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_12 : {v : ℝ // smallCoefficient weightSeven 5 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_13 : {v : ℝ // smallCoefficient weightSeven 5 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property,upper_5_moment_4.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3,upper_5_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_14 : {v : ℝ // smallCoefficient weightSeven 5 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property,upper_5_moment_4.property,upper_5_moment_5.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3,upper_5_moment_4,upper_5_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_22 : {v : ℝ // smallCoefficient weightSeven 5 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property,upper_5_moment_4.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3,upper_5_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_23 : {v : ℝ // smallCoefficient weightSeven 5 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property,upper_5_moment_4.property,upper_5_moment_5.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3,upper_5_moment_4,upper_5_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_24 : {v : ℝ // smallCoefficient weightSeven 5 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property,upper_5_moment_4.property,upper_5_moment_5.property,upper_5_moment_6.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3,upper_5_moment_4,upper_5_moment_5,upper_5_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_33 : {v : ℝ // smallCoefficient weightSeven 5 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property,upper_5_moment_4.property,upper_5_moment_5.property,upper_5_moment_6.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3,upper_5_moment_4,upper_5_moment_5,upper_5_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_34 : {v : ℝ // smallCoefficient weightSeven 5 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property,upper_5_moment_4.property,upper_5_moment_5.property,upper_5_moment_6.property,upper_5_moment_7.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3,upper_5_moment_4,upper_5_moment_5,upper_5_moment_6,upper_5_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_cell_44 : {v : ℝ // smallCoefficient weightSeven 5 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_5_moment_0.property,upper_5_moment_1.property,upper_5_moment_2.property,upper_5_moment_3.property,upper_5_moment_4.property,upper_5_moment_5.property,upper_5_moment_6.property,upper_5_moment_7.property,upper_5_moment_8.property]
      dsimp only [upper_5_moment_0,upper_5_moment_1,upper_5_moment_2,upper_5_moment_3,upper_5_moment_4,upper_5_moment_5,upper_5_moment_6,upper_5_moment_7,upper_5_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_5_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_5_cell_00.val,upper_5_cell_01.val,upper_5_cell_02.val,upper_5_cell_03.val,upper_5_cell_04.val],
    ![upper_5_cell_01.val,upper_5_cell_11.val,upper_5_cell_12.val,upper_5_cell_13.val,upper_5_cell_14.val],
    ![upper_5_cell_02.val,upper_5_cell_12.val,upper_5_cell_22.val,upper_5_cell_23.val,upper_5_cell_24.val],
    ![upper_5_cell_03.val,upper_5_cell_13.val,upper_5_cell_23.val,upper_5_cell_33.val,upper_5_cell_34.val],
    ![upper_5_cell_04.val,upper_5_cell_14.val,upper_5_cell_24.val,upper_5_cell_34.val,upper_5_cell_44.val]]

private theorem upper_5_matrix_eq : smallCoefficient weightSeven 5=upper_5_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_5_cell_00.property
  · exact upper_5_cell_01.property
  · exact upper_5_cell_02.property
  · exact upper_5_cell_03.property
  · exact upper_5_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 5 1 0).trans upper_5_cell_01.property
  · exact upper_5_cell_11.property
  · exact upper_5_cell_12.property
  · exact upper_5_cell_13.property
  · exact upper_5_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 5 2 0).trans upper_5_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 5 2 1).trans upper_5_cell_12.property
  · exact upper_5_cell_22.property
  · exact upper_5_cell_23.property
  · exact upper_5_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 5 3 0).trans upper_5_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 5 3 1).trans upper_5_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 5 3 2).trans upper_5_cell_23.property
  · exact upper_5_cell_33.property
  · exact upper_5_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 5 4 0).trans upper_5_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 5 4 1).trans upper_5_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 5 4 2).trans upper_5_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 5 4 3).trans upper_5_cell_34.property
  · exact upper_5_cell_44.property

private theorem upper_5_first_pos : 0 < upper_5_matrix 0 0 := by
  dsimp only [upper_5_matrix,upper_5_cell_00,upper_5_cell_01,upper_5_cell_02,upper_5_cell_03,upper_5_cell_04,upper_5_cell_11,upper_5_cell_12,upper_5_cell_13,upper_5_cell_14,upper_5_cell_22,upper_5_cell_23,upper_5_cell_24,upper_5_cell_33,upper_5_cell_34,upper_5_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_5_delta_pos : 0 < delta upper_5_matrix := by
  dsimp only [upper_5_matrix,upper_5_cell_00,upper_5_cell_01,upper_5_cell_02,upper_5_cell_03,upper_5_cell_04,upper_5_cell_11,upper_5_cell_12,upper_5_cell_13,upper_5_cell_14,upper_5_cell_22,upper_5_cell_23,upper_5_cell_24,upper_5_cell_33,upper_5_cell_34,upper_5_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_5_schur_pos : 0 < schur upper_5_matrix 0 0 := by
  dsimp only [upper_5_matrix,upper_5_cell_00,upper_5_cell_01,upper_5_cell_02,upper_5_cell_03,upper_5_cell_04,upper_5_cell_11,upper_5_cell_12,upper_5_cell_13,upper_5_cell_14,upper_5_cell_22,upper_5_cell_23,upper_5_cell_24,upper_5_cell_33,upper_5_cell_34,upper_5_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_5_minor_pos : 0 < minor upper_5_matrix := by
  dsimp only [upper_5_matrix,upper_5_cell_00,upper_5_cell_01,upper_5_cell_02,upper_5_cell_03,upper_5_cell_04,upper_5_cell_11,upper_5_cell_12,upper_5_cell_13,upper_5_cell_14,upper_5_cell_22,upper_5_cell_23,upper_5_cell_24,upper_5_cell_33,upper_5_cell_34,upper_5_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_5_det_pos : 0 < determinant upper_5_matrix := by
  dsimp only [upper_5_matrix,upper_5_cell_00,upper_5_cell_01,upper_5_cell_02,upper_5_cell_03,upper_5_cell_04,upper_5_cell_11,upper_5_cell_12,upper_5_cell_13,upper_5_cell_14,upper_5_cell_22,upper_5_cell_23,upper_5_cell_24,upper_5_cell_33,upper_5_cell_34,upper_5_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_5_matrix_posDef : upper_5_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_5_first_pos upper_5_delta_pos upper_5_schur_pos
    upper_5_minor_pos upper_5_det_pos
  intro i j
  rw [← upper_5_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 5 i j

private theorem upper_5_posDef : (smallCoefficient weightSeven 5).PosDef := by
  rw [upper_5_matrix_eq]
  exact upper_5_matrix_posDef


private def upper_6_moment_0 : {v : ℝ // momentCoefficient weightSeven 6 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_6_moment_1 : {v : ℝ // momentCoefficient weightSeven 6 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_6_moment_2 : {v : ℝ // momentCoefficient weightSeven 6 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_6_moment_3 : {v : ℝ // momentCoefficient weightSeven 6 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_6_moment_4 : {v : ℝ // momentCoefficient weightSeven 6 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_6_moment_5 : {v : ℝ // momentCoefficient weightSeven 6 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_6_moment_6 : {v : ℝ // momentCoefficient weightSeven 6 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_6_moment_7 : {v : ℝ // momentCoefficient weightSeven 6 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_6_moment_8 : {v : ℝ // momentCoefficient weightSeven 6 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_6_cell_00 : {v : ℝ // smallCoefficient weightSeven 6 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_6_moment_0.property]
      dsimp only [upper_6_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_01 : {v : ℝ // smallCoefficient weightSeven 6 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_6_moment_0.property,upper_6_moment_1.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_02 : {v : ℝ // smallCoefficient weightSeven 6 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_03 : {v : ℝ // smallCoefficient weightSeven 6 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_04 : {v : ℝ // smallCoefficient weightSeven 6 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property,upper_6_moment_4.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3,upper_6_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_11 : {v : ℝ // smallCoefficient weightSeven 6 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_12 : {v : ℝ // smallCoefficient weightSeven 6 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_13 : {v : ℝ // smallCoefficient weightSeven 6 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property,upper_6_moment_4.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3,upper_6_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_14 : {v : ℝ // smallCoefficient weightSeven 6 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property,upper_6_moment_4.property,upper_6_moment_5.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3,upper_6_moment_4,upper_6_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_22 : {v : ℝ // smallCoefficient weightSeven 6 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property,upper_6_moment_4.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3,upper_6_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_23 : {v : ℝ // smallCoefficient weightSeven 6 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property,upper_6_moment_4.property,upper_6_moment_5.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3,upper_6_moment_4,upper_6_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_24 : {v : ℝ // smallCoefficient weightSeven 6 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property,upper_6_moment_4.property,upper_6_moment_5.property,upper_6_moment_6.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3,upper_6_moment_4,upper_6_moment_5,upper_6_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_33 : {v : ℝ // smallCoefficient weightSeven 6 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property,upper_6_moment_4.property,upper_6_moment_5.property,upper_6_moment_6.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3,upper_6_moment_4,upper_6_moment_5,upper_6_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_34 : {v : ℝ // smallCoefficient weightSeven 6 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property,upper_6_moment_4.property,upper_6_moment_5.property,upper_6_moment_6.property,upper_6_moment_7.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3,upper_6_moment_4,upper_6_moment_5,upper_6_moment_6,upper_6_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_cell_44 : {v : ℝ // smallCoefficient weightSeven 6 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_6_moment_0.property,upper_6_moment_1.property,upper_6_moment_2.property,upper_6_moment_3.property,upper_6_moment_4.property,upper_6_moment_5.property,upper_6_moment_6.property,upper_6_moment_7.property,upper_6_moment_8.property]
      dsimp only [upper_6_moment_0,upper_6_moment_1,upper_6_moment_2,upper_6_moment_3,upper_6_moment_4,upper_6_moment_5,upper_6_moment_6,upper_6_moment_7,upper_6_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_6_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_6_cell_00.val,upper_6_cell_01.val,upper_6_cell_02.val,upper_6_cell_03.val,upper_6_cell_04.val],
    ![upper_6_cell_01.val,upper_6_cell_11.val,upper_6_cell_12.val,upper_6_cell_13.val,upper_6_cell_14.val],
    ![upper_6_cell_02.val,upper_6_cell_12.val,upper_6_cell_22.val,upper_6_cell_23.val,upper_6_cell_24.val],
    ![upper_6_cell_03.val,upper_6_cell_13.val,upper_6_cell_23.val,upper_6_cell_33.val,upper_6_cell_34.val],
    ![upper_6_cell_04.val,upper_6_cell_14.val,upper_6_cell_24.val,upper_6_cell_34.val,upper_6_cell_44.val]]

private theorem upper_6_matrix_eq : smallCoefficient weightSeven 6=upper_6_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_6_cell_00.property
  · exact upper_6_cell_01.property
  · exact upper_6_cell_02.property
  · exact upper_6_cell_03.property
  · exact upper_6_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 6 1 0).trans upper_6_cell_01.property
  · exact upper_6_cell_11.property
  · exact upper_6_cell_12.property
  · exact upper_6_cell_13.property
  · exact upper_6_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 6 2 0).trans upper_6_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 6 2 1).trans upper_6_cell_12.property
  · exact upper_6_cell_22.property
  · exact upper_6_cell_23.property
  · exact upper_6_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 6 3 0).trans upper_6_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 6 3 1).trans upper_6_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 6 3 2).trans upper_6_cell_23.property
  · exact upper_6_cell_33.property
  · exact upper_6_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 6 4 0).trans upper_6_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 6 4 1).trans upper_6_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 6 4 2).trans upper_6_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 6 4 3).trans upper_6_cell_34.property
  · exact upper_6_cell_44.property

private theorem upper_6_first_pos : 0 < upper_6_matrix 0 0 := by
  dsimp only [upper_6_matrix,upper_6_cell_00,upper_6_cell_01,upper_6_cell_02,upper_6_cell_03,upper_6_cell_04,upper_6_cell_11,upper_6_cell_12,upper_6_cell_13,upper_6_cell_14,upper_6_cell_22,upper_6_cell_23,upper_6_cell_24,upper_6_cell_33,upper_6_cell_34,upper_6_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_6_delta_pos : 0 < delta upper_6_matrix := by
  dsimp only [upper_6_matrix,upper_6_cell_00,upper_6_cell_01,upper_6_cell_02,upper_6_cell_03,upper_6_cell_04,upper_6_cell_11,upper_6_cell_12,upper_6_cell_13,upper_6_cell_14,upper_6_cell_22,upper_6_cell_23,upper_6_cell_24,upper_6_cell_33,upper_6_cell_34,upper_6_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_6_schur_pos : 0 < schur upper_6_matrix 0 0 := by
  dsimp only [upper_6_matrix,upper_6_cell_00,upper_6_cell_01,upper_6_cell_02,upper_6_cell_03,upper_6_cell_04,upper_6_cell_11,upper_6_cell_12,upper_6_cell_13,upper_6_cell_14,upper_6_cell_22,upper_6_cell_23,upper_6_cell_24,upper_6_cell_33,upper_6_cell_34,upper_6_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_6_minor_pos : 0 < minor upper_6_matrix := by
  dsimp only [upper_6_matrix,upper_6_cell_00,upper_6_cell_01,upper_6_cell_02,upper_6_cell_03,upper_6_cell_04,upper_6_cell_11,upper_6_cell_12,upper_6_cell_13,upper_6_cell_14,upper_6_cell_22,upper_6_cell_23,upper_6_cell_24,upper_6_cell_33,upper_6_cell_34,upper_6_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_6_det_pos : 0 < determinant upper_6_matrix := by
  dsimp only [upper_6_matrix,upper_6_cell_00,upper_6_cell_01,upper_6_cell_02,upper_6_cell_03,upper_6_cell_04,upper_6_cell_11,upper_6_cell_12,upper_6_cell_13,upper_6_cell_14,upper_6_cell_22,upper_6_cell_23,upper_6_cell_24,upper_6_cell_33,upper_6_cell_34,upper_6_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_6_matrix_posDef : upper_6_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_6_first_pos upper_6_delta_pos upper_6_schur_pos
    upper_6_minor_pos upper_6_det_pos
  intro i j
  rw [← upper_6_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 6 i j

private theorem upper_6_posDef : (smallCoefficient weightSeven 6).PosDef := by
  rw [upper_6_matrix_eq]
  exact upper_6_matrix_posDef


private def upper_7_moment_0 : {v : ℝ // momentCoefficient weightSeven 7 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_7_moment_1 : {v : ℝ // momentCoefficient weightSeven 7 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_7_moment_2 : {v : ℝ // momentCoefficient weightSeven 7 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_7_moment_3 : {v : ℝ // momentCoefficient weightSeven 7 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_7_moment_4 : {v : ℝ // momentCoefficient weightSeven 7 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_7_moment_5 : {v : ℝ // momentCoefficient weightSeven 7 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_7_moment_6 : {v : ℝ // momentCoefficient weightSeven 7 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_7_moment_7 : {v : ℝ // momentCoefficient weightSeven 7 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_7_moment_8 : {v : ℝ // momentCoefficient weightSeven 7 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_7_cell_00 : {v : ℝ // smallCoefficient weightSeven 7 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_7_moment_0.property]
      dsimp only [upper_7_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_01 : {v : ℝ // smallCoefficient weightSeven 7 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_7_moment_0.property,upper_7_moment_1.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_02 : {v : ℝ // smallCoefficient weightSeven 7 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_03 : {v : ℝ // smallCoefficient weightSeven 7 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_04 : {v : ℝ // smallCoefficient weightSeven 7 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property,upper_7_moment_4.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3,upper_7_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_11 : {v : ℝ // smallCoefficient weightSeven 7 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_12 : {v : ℝ // smallCoefficient weightSeven 7 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_13 : {v : ℝ // smallCoefficient weightSeven 7 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property,upper_7_moment_4.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3,upper_7_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_14 : {v : ℝ // smallCoefficient weightSeven 7 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property,upper_7_moment_4.property,upper_7_moment_5.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3,upper_7_moment_4,upper_7_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_22 : {v : ℝ // smallCoefficient weightSeven 7 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property,upper_7_moment_4.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3,upper_7_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_23 : {v : ℝ // smallCoefficient weightSeven 7 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property,upper_7_moment_4.property,upper_7_moment_5.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3,upper_7_moment_4,upper_7_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_24 : {v : ℝ // smallCoefficient weightSeven 7 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property,upper_7_moment_4.property,upper_7_moment_5.property,upper_7_moment_6.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3,upper_7_moment_4,upper_7_moment_5,upper_7_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_33 : {v : ℝ // smallCoefficient weightSeven 7 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property,upper_7_moment_4.property,upper_7_moment_5.property,upper_7_moment_6.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3,upper_7_moment_4,upper_7_moment_5,upper_7_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_34 : {v : ℝ // smallCoefficient weightSeven 7 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property,upper_7_moment_4.property,upper_7_moment_5.property,upper_7_moment_6.property,upper_7_moment_7.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3,upper_7_moment_4,upper_7_moment_5,upper_7_moment_6,upper_7_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_cell_44 : {v : ℝ // smallCoefficient weightSeven 7 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_7_moment_0.property,upper_7_moment_1.property,upper_7_moment_2.property,upper_7_moment_3.property,upper_7_moment_4.property,upper_7_moment_5.property,upper_7_moment_6.property,upper_7_moment_7.property,upper_7_moment_8.property]
      dsimp only [upper_7_moment_0,upper_7_moment_1,upper_7_moment_2,upper_7_moment_3,upper_7_moment_4,upper_7_moment_5,upper_7_moment_6,upper_7_moment_7,upper_7_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_7_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_7_cell_00.val,upper_7_cell_01.val,upper_7_cell_02.val,upper_7_cell_03.val,upper_7_cell_04.val],
    ![upper_7_cell_01.val,upper_7_cell_11.val,upper_7_cell_12.val,upper_7_cell_13.val,upper_7_cell_14.val],
    ![upper_7_cell_02.val,upper_7_cell_12.val,upper_7_cell_22.val,upper_7_cell_23.val,upper_7_cell_24.val],
    ![upper_7_cell_03.val,upper_7_cell_13.val,upper_7_cell_23.val,upper_7_cell_33.val,upper_7_cell_34.val],
    ![upper_7_cell_04.val,upper_7_cell_14.val,upper_7_cell_24.val,upper_7_cell_34.val,upper_7_cell_44.val]]

private theorem upper_7_matrix_eq : smallCoefficient weightSeven 7=upper_7_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_7_cell_00.property
  · exact upper_7_cell_01.property
  · exact upper_7_cell_02.property
  · exact upper_7_cell_03.property
  · exact upper_7_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 7 1 0).trans upper_7_cell_01.property
  · exact upper_7_cell_11.property
  · exact upper_7_cell_12.property
  · exact upper_7_cell_13.property
  · exact upper_7_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 7 2 0).trans upper_7_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 7 2 1).trans upper_7_cell_12.property
  · exact upper_7_cell_22.property
  · exact upper_7_cell_23.property
  · exact upper_7_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 7 3 0).trans upper_7_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 7 3 1).trans upper_7_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 7 3 2).trans upper_7_cell_23.property
  · exact upper_7_cell_33.property
  · exact upper_7_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 7 4 0).trans upper_7_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 7 4 1).trans upper_7_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 7 4 2).trans upper_7_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 7 4 3).trans upper_7_cell_34.property
  · exact upper_7_cell_44.property

private theorem upper_7_first_pos : 0 < upper_7_matrix 0 0 := by
  dsimp only [upper_7_matrix,upper_7_cell_00,upper_7_cell_01,upper_7_cell_02,upper_7_cell_03,upper_7_cell_04,upper_7_cell_11,upper_7_cell_12,upper_7_cell_13,upper_7_cell_14,upper_7_cell_22,upper_7_cell_23,upper_7_cell_24,upper_7_cell_33,upper_7_cell_34,upper_7_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_7_delta_pos : 0 < delta upper_7_matrix := by
  dsimp only [upper_7_matrix,upper_7_cell_00,upper_7_cell_01,upper_7_cell_02,upper_7_cell_03,upper_7_cell_04,upper_7_cell_11,upper_7_cell_12,upper_7_cell_13,upper_7_cell_14,upper_7_cell_22,upper_7_cell_23,upper_7_cell_24,upper_7_cell_33,upper_7_cell_34,upper_7_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_7_schur_pos : 0 < schur upper_7_matrix 0 0 := by
  dsimp only [upper_7_matrix,upper_7_cell_00,upper_7_cell_01,upper_7_cell_02,upper_7_cell_03,upper_7_cell_04,upper_7_cell_11,upper_7_cell_12,upper_7_cell_13,upper_7_cell_14,upper_7_cell_22,upper_7_cell_23,upper_7_cell_24,upper_7_cell_33,upper_7_cell_34,upper_7_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_7_minor_pos : 0 < minor upper_7_matrix := by
  dsimp only [upper_7_matrix,upper_7_cell_00,upper_7_cell_01,upper_7_cell_02,upper_7_cell_03,upper_7_cell_04,upper_7_cell_11,upper_7_cell_12,upper_7_cell_13,upper_7_cell_14,upper_7_cell_22,upper_7_cell_23,upper_7_cell_24,upper_7_cell_33,upper_7_cell_34,upper_7_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_7_det_pos : 0 < determinant upper_7_matrix := by
  dsimp only [upper_7_matrix,upper_7_cell_00,upper_7_cell_01,upper_7_cell_02,upper_7_cell_03,upper_7_cell_04,upper_7_cell_11,upper_7_cell_12,upper_7_cell_13,upper_7_cell_14,upper_7_cell_22,upper_7_cell_23,upper_7_cell_24,upper_7_cell_33,upper_7_cell_34,upper_7_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_7_matrix_posDef : upper_7_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_7_first_pos upper_7_delta_pos upper_7_schur_pos
    upper_7_minor_pos upper_7_det_pos
  intro i j
  rw [← upper_7_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 7 i j

private theorem upper_7_posDef : (smallCoefficient weightSeven 7).PosDef := by
  rw [upper_7_matrix_eq]
  exact upper_7_matrix_posDef


private def upper_8_moment_0 : {v : ℝ // momentCoefficient weightSeven 8 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_8_moment_1 : {v : ℝ // momentCoefficient weightSeven 8 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_8_moment_2 : {v : ℝ // momentCoefficient weightSeven 8 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_8_moment_3 : {v : ℝ // momentCoefficient weightSeven 8 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_8_moment_4 : {v : ℝ // momentCoefficient weightSeven 8 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_8_moment_5 : {v : ℝ // momentCoefficient weightSeven 8 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_8_moment_6 : {v : ℝ // momentCoefficient weightSeven 8 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_8_moment_7 : {v : ℝ // momentCoefficient weightSeven 8 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_8_moment_8 : {v : ℝ // momentCoefficient weightSeven 8 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_8_cell_00 : {v : ℝ // smallCoefficient weightSeven 8 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_8_moment_0.property]
      dsimp only [upper_8_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_01 : {v : ℝ // smallCoefficient weightSeven 8 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_8_moment_0.property,upper_8_moment_1.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_02 : {v : ℝ // smallCoefficient weightSeven 8 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_03 : {v : ℝ // smallCoefficient weightSeven 8 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_04 : {v : ℝ // smallCoefficient weightSeven 8 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property,upper_8_moment_4.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3,upper_8_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_11 : {v : ℝ // smallCoefficient weightSeven 8 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_12 : {v : ℝ // smallCoefficient weightSeven 8 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_13 : {v : ℝ // smallCoefficient weightSeven 8 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property,upper_8_moment_4.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3,upper_8_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_14 : {v : ℝ // smallCoefficient weightSeven 8 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property,upper_8_moment_4.property,upper_8_moment_5.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3,upper_8_moment_4,upper_8_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_22 : {v : ℝ // smallCoefficient weightSeven 8 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property,upper_8_moment_4.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3,upper_8_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_23 : {v : ℝ // smallCoefficient weightSeven 8 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property,upper_8_moment_4.property,upper_8_moment_5.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3,upper_8_moment_4,upper_8_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_24 : {v : ℝ // smallCoefficient weightSeven 8 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property,upper_8_moment_4.property,upper_8_moment_5.property,upper_8_moment_6.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3,upper_8_moment_4,upper_8_moment_5,upper_8_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_33 : {v : ℝ // smallCoefficient weightSeven 8 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property,upper_8_moment_4.property,upper_8_moment_5.property,upper_8_moment_6.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3,upper_8_moment_4,upper_8_moment_5,upper_8_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_34 : {v : ℝ // smallCoefficient weightSeven 8 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property,upper_8_moment_4.property,upper_8_moment_5.property,upper_8_moment_6.property,upper_8_moment_7.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3,upper_8_moment_4,upper_8_moment_5,upper_8_moment_6,upper_8_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_cell_44 : {v : ℝ // smallCoefficient weightSeven 8 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_8_moment_0.property,upper_8_moment_1.property,upper_8_moment_2.property,upper_8_moment_3.property,upper_8_moment_4.property,upper_8_moment_5.property,upper_8_moment_6.property,upper_8_moment_7.property,upper_8_moment_8.property]
      dsimp only [upper_8_moment_0,upper_8_moment_1,upper_8_moment_2,upper_8_moment_3,upper_8_moment_4,upper_8_moment_5,upper_8_moment_6,upper_8_moment_7,upper_8_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_8_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_8_cell_00.val,upper_8_cell_01.val,upper_8_cell_02.val,upper_8_cell_03.val,upper_8_cell_04.val],
    ![upper_8_cell_01.val,upper_8_cell_11.val,upper_8_cell_12.val,upper_8_cell_13.val,upper_8_cell_14.val],
    ![upper_8_cell_02.val,upper_8_cell_12.val,upper_8_cell_22.val,upper_8_cell_23.val,upper_8_cell_24.val],
    ![upper_8_cell_03.val,upper_8_cell_13.val,upper_8_cell_23.val,upper_8_cell_33.val,upper_8_cell_34.val],
    ![upper_8_cell_04.val,upper_8_cell_14.val,upper_8_cell_24.val,upper_8_cell_34.val,upper_8_cell_44.val]]

private theorem upper_8_matrix_eq : smallCoefficient weightSeven 8=upper_8_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_8_cell_00.property
  · exact upper_8_cell_01.property
  · exact upper_8_cell_02.property
  · exact upper_8_cell_03.property
  · exact upper_8_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 8 1 0).trans upper_8_cell_01.property
  · exact upper_8_cell_11.property
  · exact upper_8_cell_12.property
  · exact upper_8_cell_13.property
  · exact upper_8_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 8 2 0).trans upper_8_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 8 2 1).trans upper_8_cell_12.property
  · exact upper_8_cell_22.property
  · exact upper_8_cell_23.property
  · exact upper_8_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 8 3 0).trans upper_8_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 8 3 1).trans upper_8_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 8 3 2).trans upper_8_cell_23.property
  · exact upper_8_cell_33.property
  · exact upper_8_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 8 4 0).trans upper_8_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 8 4 1).trans upper_8_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 8 4 2).trans upper_8_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 8 4 3).trans upper_8_cell_34.property
  · exact upper_8_cell_44.property

private theorem upper_8_first_pos : 0 < upper_8_matrix 0 0 := by
  dsimp only [upper_8_matrix,upper_8_cell_00,upper_8_cell_01,upper_8_cell_02,upper_8_cell_03,upper_8_cell_04,upper_8_cell_11,upper_8_cell_12,upper_8_cell_13,upper_8_cell_14,upper_8_cell_22,upper_8_cell_23,upper_8_cell_24,upper_8_cell_33,upper_8_cell_34,upper_8_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_8_delta_pos : 0 < delta upper_8_matrix := by
  dsimp only [upper_8_matrix,upper_8_cell_00,upper_8_cell_01,upper_8_cell_02,upper_8_cell_03,upper_8_cell_04,upper_8_cell_11,upper_8_cell_12,upper_8_cell_13,upper_8_cell_14,upper_8_cell_22,upper_8_cell_23,upper_8_cell_24,upper_8_cell_33,upper_8_cell_34,upper_8_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_8_schur_pos : 0 < schur upper_8_matrix 0 0 := by
  dsimp only [upper_8_matrix,upper_8_cell_00,upper_8_cell_01,upper_8_cell_02,upper_8_cell_03,upper_8_cell_04,upper_8_cell_11,upper_8_cell_12,upper_8_cell_13,upper_8_cell_14,upper_8_cell_22,upper_8_cell_23,upper_8_cell_24,upper_8_cell_33,upper_8_cell_34,upper_8_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_8_minor_pos : 0 < minor upper_8_matrix := by
  dsimp only [upper_8_matrix,upper_8_cell_00,upper_8_cell_01,upper_8_cell_02,upper_8_cell_03,upper_8_cell_04,upper_8_cell_11,upper_8_cell_12,upper_8_cell_13,upper_8_cell_14,upper_8_cell_22,upper_8_cell_23,upper_8_cell_24,upper_8_cell_33,upper_8_cell_34,upper_8_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_8_det_pos : 0 < determinant upper_8_matrix := by
  dsimp only [upper_8_matrix,upper_8_cell_00,upper_8_cell_01,upper_8_cell_02,upper_8_cell_03,upper_8_cell_04,upper_8_cell_11,upper_8_cell_12,upper_8_cell_13,upper_8_cell_14,upper_8_cell_22,upper_8_cell_23,upper_8_cell_24,upper_8_cell_33,upper_8_cell_34,upper_8_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_8_matrix_posDef : upper_8_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_8_first_pos upper_8_delta_pos upper_8_schur_pos
    upper_8_minor_pos upper_8_det_pos
  intro i j
  rw [← upper_8_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 8 i j

private theorem upper_8_posDef : (smallCoefficient weightSeven 8).PosDef := by
  rw [upper_8_matrix_eq]
  exact upper_8_matrix_posDef


private def upper_9_moment_0 : {v : ℝ // momentCoefficient weightSeven 9 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_9_moment_1 : {v : ℝ // momentCoefficient weightSeven 9 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_9_moment_2 : {v : ℝ // momentCoefficient weightSeven 9 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_9_moment_3 : {v : ℝ // momentCoefficient weightSeven 9 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_9_moment_4 : {v : ℝ // momentCoefficient weightSeven 9 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_9_moment_5 : {v : ℝ // momentCoefficient weightSeven 9 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_9_moment_6 : {v : ℝ // momentCoefficient weightSeven 9 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_9_moment_7 : {v : ℝ // momentCoefficient weightSeven 9 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_9_moment_8 : {v : ℝ // momentCoefficient weightSeven 9 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_9_cell_00 : {v : ℝ // smallCoefficient weightSeven 9 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_9_moment_0.property]
      dsimp only [upper_9_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_01 : {v : ℝ // smallCoefficient weightSeven 9 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_9_moment_0.property,upper_9_moment_1.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_02 : {v : ℝ // smallCoefficient weightSeven 9 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_03 : {v : ℝ // smallCoefficient weightSeven 9 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_04 : {v : ℝ // smallCoefficient weightSeven 9 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property,upper_9_moment_4.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3,upper_9_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_11 : {v : ℝ // smallCoefficient weightSeven 9 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_12 : {v : ℝ // smallCoefficient weightSeven 9 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_13 : {v : ℝ // smallCoefficient weightSeven 9 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property,upper_9_moment_4.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3,upper_9_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_14 : {v : ℝ // smallCoefficient weightSeven 9 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property,upper_9_moment_4.property,upper_9_moment_5.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3,upper_9_moment_4,upper_9_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_22 : {v : ℝ // smallCoefficient weightSeven 9 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property,upper_9_moment_4.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3,upper_9_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_23 : {v : ℝ // smallCoefficient weightSeven 9 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property,upper_9_moment_4.property,upper_9_moment_5.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3,upper_9_moment_4,upper_9_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_24 : {v : ℝ // smallCoefficient weightSeven 9 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property,upper_9_moment_4.property,upper_9_moment_5.property,upper_9_moment_6.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3,upper_9_moment_4,upper_9_moment_5,upper_9_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_33 : {v : ℝ // smallCoefficient weightSeven 9 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property,upper_9_moment_4.property,upper_9_moment_5.property,upper_9_moment_6.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3,upper_9_moment_4,upper_9_moment_5,upper_9_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_34 : {v : ℝ // smallCoefficient weightSeven 9 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property,upper_9_moment_4.property,upper_9_moment_5.property,upper_9_moment_6.property,upper_9_moment_7.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3,upper_9_moment_4,upper_9_moment_5,upper_9_moment_6,upper_9_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_cell_44 : {v : ℝ // smallCoefficient weightSeven 9 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_9_moment_0.property,upper_9_moment_1.property,upper_9_moment_2.property,upper_9_moment_3.property,upper_9_moment_4.property,upper_9_moment_5.property,upper_9_moment_6.property,upper_9_moment_7.property,upper_9_moment_8.property]
      dsimp only [upper_9_moment_0,upper_9_moment_1,upper_9_moment_2,upper_9_moment_3,upper_9_moment_4,upper_9_moment_5,upper_9_moment_6,upper_9_moment_7,upper_9_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_9_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_9_cell_00.val,upper_9_cell_01.val,upper_9_cell_02.val,upper_9_cell_03.val,upper_9_cell_04.val],
    ![upper_9_cell_01.val,upper_9_cell_11.val,upper_9_cell_12.val,upper_9_cell_13.val,upper_9_cell_14.val],
    ![upper_9_cell_02.val,upper_9_cell_12.val,upper_9_cell_22.val,upper_9_cell_23.val,upper_9_cell_24.val],
    ![upper_9_cell_03.val,upper_9_cell_13.val,upper_9_cell_23.val,upper_9_cell_33.val,upper_9_cell_34.val],
    ![upper_9_cell_04.val,upper_9_cell_14.val,upper_9_cell_24.val,upper_9_cell_34.val,upper_9_cell_44.val]]

private theorem upper_9_matrix_eq : smallCoefficient weightSeven 9=upper_9_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_9_cell_00.property
  · exact upper_9_cell_01.property
  · exact upper_9_cell_02.property
  · exact upper_9_cell_03.property
  · exact upper_9_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 9 1 0).trans upper_9_cell_01.property
  · exact upper_9_cell_11.property
  · exact upper_9_cell_12.property
  · exact upper_9_cell_13.property
  · exact upper_9_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 9 2 0).trans upper_9_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 9 2 1).trans upper_9_cell_12.property
  · exact upper_9_cell_22.property
  · exact upper_9_cell_23.property
  · exact upper_9_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 9 3 0).trans upper_9_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 9 3 1).trans upper_9_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 9 3 2).trans upper_9_cell_23.property
  · exact upper_9_cell_33.property
  · exact upper_9_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 9 4 0).trans upper_9_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 9 4 1).trans upper_9_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 9 4 2).trans upper_9_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 9 4 3).trans upper_9_cell_34.property
  · exact upper_9_cell_44.property

private theorem upper_9_first_pos : 0 < upper_9_matrix 0 0 := by
  dsimp only [upper_9_matrix,upper_9_cell_00,upper_9_cell_01,upper_9_cell_02,upper_9_cell_03,upper_9_cell_04,upper_9_cell_11,upper_9_cell_12,upper_9_cell_13,upper_9_cell_14,upper_9_cell_22,upper_9_cell_23,upper_9_cell_24,upper_9_cell_33,upper_9_cell_34,upper_9_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_9_delta_pos : 0 < delta upper_9_matrix := by
  dsimp only [upper_9_matrix,upper_9_cell_00,upper_9_cell_01,upper_9_cell_02,upper_9_cell_03,upper_9_cell_04,upper_9_cell_11,upper_9_cell_12,upper_9_cell_13,upper_9_cell_14,upper_9_cell_22,upper_9_cell_23,upper_9_cell_24,upper_9_cell_33,upper_9_cell_34,upper_9_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_9_schur_pos : 0 < schur upper_9_matrix 0 0 := by
  dsimp only [upper_9_matrix,upper_9_cell_00,upper_9_cell_01,upper_9_cell_02,upper_9_cell_03,upper_9_cell_04,upper_9_cell_11,upper_9_cell_12,upper_9_cell_13,upper_9_cell_14,upper_9_cell_22,upper_9_cell_23,upper_9_cell_24,upper_9_cell_33,upper_9_cell_34,upper_9_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_9_minor_pos : 0 < minor upper_9_matrix := by
  dsimp only [upper_9_matrix,upper_9_cell_00,upper_9_cell_01,upper_9_cell_02,upper_9_cell_03,upper_9_cell_04,upper_9_cell_11,upper_9_cell_12,upper_9_cell_13,upper_9_cell_14,upper_9_cell_22,upper_9_cell_23,upper_9_cell_24,upper_9_cell_33,upper_9_cell_34,upper_9_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_9_det_pos : 0 < determinant upper_9_matrix := by
  dsimp only [upper_9_matrix,upper_9_cell_00,upper_9_cell_01,upper_9_cell_02,upper_9_cell_03,upper_9_cell_04,upper_9_cell_11,upper_9_cell_12,upper_9_cell_13,upper_9_cell_14,upper_9_cell_22,upper_9_cell_23,upper_9_cell_24,upper_9_cell_33,upper_9_cell_34,upper_9_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_9_matrix_posDef : upper_9_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_9_first_pos upper_9_delta_pos upper_9_schur_pos
    upper_9_minor_pos upper_9_det_pos
  intro i j
  rw [← upper_9_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 9 i j

private theorem upper_9_posDef : (smallCoefficient weightSeven 9).PosDef := by
  rw [upper_9_matrix_eq]
  exact upper_9_matrix_posDef


private def upper_10_moment_0 : {v : ℝ // momentCoefficient weightSeven 10 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_10_moment_1 : {v : ℝ // momentCoefficient weightSeven 10 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_10_moment_2 : {v : ℝ // momentCoefficient weightSeven 10 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_10_moment_3 : {v : ℝ // momentCoefficient weightSeven 10 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_10_moment_4 : {v : ℝ // momentCoefficient weightSeven 10 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_10_moment_5 : {v : ℝ // momentCoefficient weightSeven 10 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_10_moment_6 : {v : ℝ // momentCoefficient weightSeven 10 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_10_moment_7 : {v : ℝ // momentCoefficient weightSeven 10 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_10_moment_8 : {v : ℝ // momentCoefficient weightSeven 10 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_10_cell_00 : {v : ℝ // smallCoefficient weightSeven 10 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_10_moment_0.property]
      dsimp only [upper_10_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_01 : {v : ℝ // smallCoefficient weightSeven 10 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_10_moment_0.property,upper_10_moment_1.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_02 : {v : ℝ // smallCoefficient weightSeven 10 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_03 : {v : ℝ // smallCoefficient weightSeven 10 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_04 : {v : ℝ // smallCoefficient weightSeven 10 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property,upper_10_moment_4.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3,upper_10_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_11 : {v : ℝ // smallCoefficient weightSeven 10 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_12 : {v : ℝ // smallCoefficient weightSeven 10 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_13 : {v : ℝ // smallCoefficient weightSeven 10 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property,upper_10_moment_4.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3,upper_10_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_14 : {v : ℝ // smallCoefficient weightSeven 10 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property,upper_10_moment_4.property,upper_10_moment_5.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3,upper_10_moment_4,upper_10_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_22 : {v : ℝ // smallCoefficient weightSeven 10 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property,upper_10_moment_4.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3,upper_10_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_23 : {v : ℝ // smallCoefficient weightSeven 10 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property,upper_10_moment_4.property,upper_10_moment_5.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3,upper_10_moment_4,upper_10_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_24 : {v : ℝ // smallCoefficient weightSeven 10 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property,upper_10_moment_4.property,upper_10_moment_5.property,upper_10_moment_6.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3,upper_10_moment_4,upper_10_moment_5,upper_10_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_33 : {v : ℝ // smallCoefficient weightSeven 10 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property,upper_10_moment_4.property,upper_10_moment_5.property,upper_10_moment_6.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3,upper_10_moment_4,upper_10_moment_5,upper_10_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_34 : {v : ℝ // smallCoefficient weightSeven 10 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property,upper_10_moment_4.property,upper_10_moment_5.property,upper_10_moment_6.property,upper_10_moment_7.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3,upper_10_moment_4,upper_10_moment_5,upper_10_moment_6,upper_10_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_cell_44 : {v : ℝ // smallCoefficient weightSeven 10 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_10_moment_0.property,upper_10_moment_1.property,upper_10_moment_2.property,upper_10_moment_3.property,upper_10_moment_4.property,upper_10_moment_5.property,upper_10_moment_6.property,upper_10_moment_7.property,upper_10_moment_8.property]
      dsimp only [upper_10_moment_0,upper_10_moment_1,upper_10_moment_2,upper_10_moment_3,upper_10_moment_4,upper_10_moment_5,upper_10_moment_6,upper_10_moment_7,upper_10_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_10_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_10_cell_00.val,upper_10_cell_01.val,upper_10_cell_02.val,upper_10_cell_03.val,upper_10_cell_04.val],
    ![upper_10_cell_01.val,upper_10_cell_11.val,upper_10_cell_12.val,upper_10_cell_13.val,upper_10_cell_14.val],
    ![upper_10_cell_02.val,upper_10_cell_12.val,upper_10_cell_22.val,upper_10_cell_23.val,upper_10_cell_24.val],
    ![upper_10_cell_03.val,upper_10_cell_13.val,upper_10_cell_23.val,upper_10_cell_33.val,upper_10_cell_34.val],
    ![upper_10_cell_04.val,upper_10_cell_14.val,upper_10_cell_24.val,upper_10_cell_34.val,upper_10_cell_44.val]]

private theorem upper_10_matrix_eq : smallCoefficient weightSeven 10=upper_10_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_10_cell_00.property
  · exact upper_10_cell_01.property
  · exact upper_10_cell_02.property
  · exact upper_10_cell_03.property
  · exact upper_10_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 10 1 0).trans upper_10_cell_01.property
  · exact upper_10_cell_11.property
  · exact upper_10_cell_12.property
  · exact upper_10_cell_13.property
  · exact upper_10_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 10 2 0).trans upper_10_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 10 2 1).trans upper_10_cell_12.property
  · exact upper_10_cell_22.property
  · exact upper_10_cell_23.property
  · exact upper_10_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 10 3 0).trans upper_10_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 10 3 1).trans upper_10_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 10 3 2).trans upper_10_cell_23.property
  · exact upper_10_cell_33.property
  · exact upper_10_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 10 4 0).trans upper_10_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 10 4 1).trans upper_10_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 10 4 2).trans upper_10_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 10 4 3).trans upper_10_cell_34.property
  · exact upper_10_cell_44.property

private theorem upper_10_first_pos : 0 < upper_10_matrix 0 0 := by
  dsimp only [upper_10_matrix,upper_10_cell_00,upper_10_cell_01,upper_10_cell_02,upper_10_cell_03,upper_10_cell_04,upper_10_cell_11,upper_10_cell_12,upper_10_cell_13,upper_10_cell_14,upper_10_cell_22,upper_10_cell_23,upper_10_cell_24,upper_10_cell_33,upper_10_cell_34,upper_10_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_10_delta_pos : 0 < delta upper_10_matrix := by
  dsimp only [upper_10_matrix,upper_10_cell_00,upper_10_cell_01,upper_10_cell_02,upper_10_cell_03,upper_10_cell_04,upper_10_cell_11,upper_10_cell_12,upper_10_cell_13,upper_10_cell_14,upper_10_cell_22,upper_10_cell_23,upper_10_cell_24,upper_10_cell_33,upper_10_cell_34,upper_10_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_10_schur_pos : 0 < schur upper_10_matrix 0 0 := by
  dsimp only [upper_10_matrix,upper_10_cell_00,upper_10_cell_01,upper_10_cell_02,upper_10_cell_03,upper_10_cell_04,upper_10_cell_11,upper_10_cell_12,upper_10_cell_13,upper_10_cell_14,upper_10_cell_22,upper_10_cell_23,upper_10_cell_24,upper_10_cell_33,upper_10_cell_34,upper_10_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_10_minor_pos : 0 < minor upper_10_matrix := by
  dsimp only [upper_10_matrix,upper_10_cell_00,upper_10_cell_01,upper_10_cell_02,upper_10_cell_03,upper_10_cell_04,upper_10_cell_11,upper_10_cell_12,upper_10_cell_13,upper_10_cell_14,upper_10_cell_22,upper_10_cell_23,upper_10_cell_24,upper_10_cell_33,upper_10_cell_34,upper_10_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_10_det_pos : 0 < determinant upper_10_matrix := by
  dsimp only [upper_10_matrix,upper_10_cell_00,upper_10_cell_01,upper_10_cell_02,upper_10_cell_03,upper_10_cell_04,upper_10_cell_11,upper_10_cell_12,upper_10_cell_13,upper_10_cell_14,upper_10_cell_22,upper_10_cell_23,upper_10_cell_24,upper_10_cell_33,upper_10_cell_34,upper_10_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_10_matrix_posDef : upper_10_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_10_first_pos upper_10_delta_pos upper_10_schur_pos
    upper_10_minor_pos upper_10_det_pos
  intro i j
  rw [← upper_10_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 10 i j

private theorem upper_10_posDef : (smallCoefficient weightSeven 10).PosDef := by
  rw [upper_10_matrix_eq]
  exact upper_10_matrix_posDef


private def upper_11_moment_0 : {v : ℝ // momentCoefficient weightSeven 11 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_11_moment_1 : {v : ℝ // momentCoefficient weightSeven 11 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_11_moment_2 : {v : ℝ // momentCoefficient weightSeven 11 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_11_moment_3 : {v : ℝ // momentCoefficient weightSeven 11 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_11_moment_4 : {v : ℝ // momentCoefficient weightSeven 11 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_11_moment_5 : {v : ℝ // momentCoefficient weightSeven 11 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_11_moment_6 : {v : ℝ // momentCoefficient weightSeven 11 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_11_moment_7 : {v : ℝ // momentCoefficient weightSeven 11 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_11_moment_8 : {v : ℝ // momentCoefficient weightSeven 11 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_11_cell_00 : {v : ℝ // smallCoefficient weightSeven 11 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_11_moment_0.property]
      dsimp only [upper_11_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_01 : {v : ℝ // smallCoefficient weightSeven 11 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_11_moment_0.property,upper_11_moment_1.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_02 : {v : ℝ // smallCoefficient weightSeven 11 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_03 : {v : ℝ // smallCoefficient weightSeven 11 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_04 : {v : ℝ // smallCoefficient weightSeven 11 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property,upper_11_moment_4.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3,upper_11_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_11 : {v : ℝ // smallCoefficient weightSeven 11 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_12 : {v : ℝ // smallCoefficient weightSeven 11 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_13 : {v : ℝ // smallCoefficient weightSeven 11 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property,upper_11_moment_4.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3,upper_11_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_14 : {v : ℝ // smallCoefficient weightSeven 11 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property,upper_11_moment_4.property,upper_11_moment_5.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3,upper_11_moment_4,upper_11_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_22 : {v : ℝ // smallCoefficient weightSeven 11 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property,upper_11_moment_4.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3,upper_11_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_23 : {v : ℝ // smallCoefficient weightSeven 11 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property,upper_11_moment_4.property,upper_11_moment_5.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3,upper_11_moment_4,upper_11_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_24 : {v : ℝ // smallCoefficient weightSeven 11 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property,upper_11_moment_4.property,upper_11_moment_5.property,upper_11_moment_6.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3,upper_11_moment_4,upper_11_moment_5,upper_11_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_33 : {v : ℝ // smallCoefficient weightSeven 11 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property,upper_11_moment_4.property,upper_11_moment_5.property,upper_11_moment_6.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3,upper_11_moment_4,upper_11_moment_5,upper_11_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_34 : {v : ℝ // smallCoefficient weightSeven 11 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property,upper_11_moment_4.property,upper_11_moment_5.property,upper_11_moment_6.property,upper_11_moment_7.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3,upper_11_moment_4,upper_11_moment_5,upper_11_moment_6,upper_11_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_cell_44 : {v : ℝ // smallCoefficient weightSeven 11 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_11_moment_0.property,upper_11_moment_1.property,upper_11_moment_2.property,upper_11_moment_3.property,upper_11_moment_4.property,upper_11_moment_5.property,upper_11_moment_6.property,upper_11_moment_7.property,upper_11_moment_8.property]
      dsimp only [upper_11_moment_0,upper_11_moment_1,upper_11_moment_2,upper_11_moment_3,upper_11_moment_4,upper_11_moment_5,upper_11_moment_6,upper_11_moment_7,upper_11_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_11_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_11_cell_00.val,upper_11_cell_01.val,upper_11_cell_02.val,upper_11_cell_03.val,upper_11_cell_04.val],
    ![upper_11_cell_01.val,upper_11_cell_11.val,upper_11_cell_12.val,upper_11_cell_13.val,upper_11_cell_14.val],
    ![upper_11_cell_02.val,upper_11_cell_12.val,upper_11_cell_22.val,upper_11_cell_23.val,upper_11_cell_24.val],
    ![upper_11_cell_03.val,upper_11_cell_13.val,upper_11_cell_23.val,upper_11_cell_33.val,upper_11_cell_34.val],
    ![upper_11_cell_04.val,upper_11_cell_14.val,upper_11_cell_24.val,upper_11_cell_34.val,upper_11_cell_44.val]]

private theorem upper_11_matrix_eq : smallCoefficient weightSeven 11=upper_11_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_11_cell_00.property
  · exact upper_11_cell_01.property
  · exact upper_11_cell_02.property
  · exact upper_11_cell_03.property
  · exact upper_11_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 11 1 0).trans upper_11_cell_01.property
  · exact upper_11_cell_11.property
  · exact upper_11_cell_12.property
  · exact upper_11_cell_13.property
  · exact upper_11_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 11 2 0).trans upper_11_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 11 2 1).trans upper_11_cell_12.property
  · exact upper_11_cell_22.property
  · exact upper_11_cell_23.property
  · exact upper_11_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 11 3 0).trans upper_11_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 11 3 1).trans upper_11_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 11 3 2).trans upper_11_cell_23.property
  · exact upper_11_cell_33.property
  · exact upper_11_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 11 4 0).trans upper_11_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 11 4 1).trans upper_11_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 11 4 2).trans upper_11_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 11 4 3).trans upper_11_cell_34.property
  · exact upper_11_cell_44.property

private theorem upper_11_first_pos : 0 < upper_11_matrix 0 0 := by
  dsimp only [upper_11_matrix,upper_11_cell_00,upper_11_cell_01,upper_11_cell_02,upper_11_cell_03,upper_11_cell_04,upper_11_cell_11,upper_11_cell_12,upper_11_cell_13,upper_11_cell_14,upper_11_cell_22,upper_11_cell_23,upper_11_cell_24,upper_11_cell_33,upper_11_cell_34,upper_11_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_11_delta_pos : 0 < delta upper_11_matrix := by
  dsimp only [upper_11_matrix,upper_11_cell_00,upper_11_cell_01,upper_11_cell_02,upper_11_cell_03,upper_11_cell_04,upper_11_cell_11,upper_11_cell_12,upper_11_cell_13,upper_11_cell_14,upper_11_cell_22,upper_11_cell_23,upper_11_cell_24,upper_11_cell_33,upper_11_cell_34,upper_11_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_11_schur_pos : 0 < schur upper_11_matrix 0 0 := by
  dsimp only [upper_11_matrix,upper_11_cell_00,upper_11_cell_01,upper_11_cell_02,upper_11_cell_03,upper_11_cell_04,upper_11_cell_11,upper_11_cell_12,upper_11_cell_13,upper_11_cell_14,upper_11_cell_22,upper_11_cell_23,upper_11_cell_24,upper_11_cell_33,upper_11_cell_34,upper_11_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_11_minor_pos : 0 < minor upper_11_matrix := by
  dsimp only [upper_11_matrix,upper_11_cell_00,upper_11_cell_01,upper_11_cell_02,upper_11_cell_03,upper_11_cell_04,upper_11_cell_11,upper_11_cell_12,upper_11_cell_13,upper_11_cell_14,upper_11_cell_22,upper_11_cell_23,upper_11_cell_24,upper_11_cell_33,upper_11_cell_34,upper_11_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_11_det_pos : 0 < determinant upper_11_matrix := by
  dsimp only [upper_11_matrix,upper_11_cell_00,upper_11_cell_01,upper_11_cell_02,upper_11_cell_03,upper_11_cell_04,upper_11_cell_11,upper_11_cell_12,upper_11_cell_13,upper_11_cell_14,upper_11_cell_22,upper_11_cell_23,upper_11_cell_24,upper_11_cell_33,upper_11_cell_34,upper_11_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_11_matrix_posDef : upper_11_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_11_first_pos upper_11_delta_pos upper_11_schur_pos
    upper_11_minor_pos upper_11_det_pos
  intro i j
  rw [← upper_11_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 11 i j

private theorem upper_11_posDef : (smallCoefficient weightSeven 11).PosDef := by
  rw [upper_11_matrix_eq]
  exact upper_11_matrix_posDef


private def upper_12_moment_0 : {v : ℝ // momentCoefficient weightSeven 12 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_12_moment_1 : {v : ℝ // momentCoefficient weightSeven 12 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_12_moment_2 : {v : ℝ // momentCoefficient weightSeven 12 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_12_moment_3 : {v : ℝ // momentCoefficient weightSeven 12 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_12_moment_4 : {v : ℝ // momentCoefficient weightSeven 12 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_12_moment_5 : {v : ℝ // momentCoefficient weightSeven 12 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_12_moment_6 : {v : ℝ // momentCoefficient weightSeven 12 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_12_moment_7 : {v : ℝ // momentCoefficient weightSeven 12 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_12_moment_8 : {v : ℝ // momentCoefficient weightSeven 12 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_12_cell_00 : {v : ℝ // smallCoefficient weightSeven 12 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_12_moment_0.property]
      dsimp only [upper_12_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_01 : {v : ℝ // smallCoefficient weightSeven 12 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_12_moment_0.property,upper_12_moment_1.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_02 : {v : ℝ // smallCoefficient weightSeven 12 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_03 : {v : ℝ // smallCoefficient weightSeven 12 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_04 : {v : ℝ // smallCoefficient weightSeven 12 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property,upper_12_moment_4.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3,upper_12_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_11 : {v : ℝ // smallCoefficient weightSeven 12 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_12 : {v : ℝ // smallCoefficient weightSeven 12 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_13 : {v : ℝ // smallCoefficient weightSeven 12 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property,upper_12_moment_4.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3,upper_12_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_14 : {v : ℝ // smallCoefficient weightSeven 12 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property,upper_12_moment_4.property,upper_12_moment_5.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3,upper_12_moment_4,upper_12_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_22 : {v : ℝ // smallCoefficient weightSeven 12 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property,upper_12_moment_4.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3,upper_12_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_23 : {v : ℝ // smallCoefficient weightSeven 12 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property,upper_12_moment_4.property,upper_12_moment_5.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3,upper_12_moment_4,upper_12_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_24 : {v : ℝ // smallCoefficient weightSeven 12 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property,upper_12_moment_4.property,upper_12_moment_5.property,upper_12_moment_6.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3,upper_12_moment_4,upper_12_moment_5,upper_12_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_33 : {v : ℝ // smallCoefficient weightSeven 12 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property,upper_12_moment_4.property,upper_12_moment_5.property,upper_12_moment_6.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3,upper_12_moment_4,upper_12_moment_5,upper_12_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_34 : {v : ℝ // smallCoefficient weightSeven 12 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property,upper_12_moment_4.property,upper_12_moment_5.property,upper_12_moment_6.property,upper_12_moment_7.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3,upper_12_moment_4,upper_12_moment_5,upper_12_moment_6,upper_12_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_cell_44 : {v : ℝ // smallCoefficient weightSeven 12 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_12_moment_0.property,upper_12_moment_1.property,upper_12_moment_2.property,upper_12_moment_3.property,upper_12_moment_4.property,upper_12_moment_5.property,upper_12_moment_6.property,upper_12_moment_7.property,upper_12_moment_8.property]
      dsimp only [upper_12_moment_0,upper_12_moment_1,upper_12_moment_2,upper_12_moment_3,upper_12_moment_4,upper_12_moment_5,upper_12_moment_6,upper_12_moment_7,upper_12_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_12_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_12_cell_00.val,upper_12_cell_01.val,upper_12_cell_02.val,upper_12_cell_03.val,upper_12_cell_04.val],
    ![upper_12_cell_01.val,upper_12_cell_11.val,upper_12_cell_12.val,upper_12_cell_13.val,upper_12_cell_14.val],
    ![upper_12_cell_02.val,upper_12_cell_12.val,upper_12_cell_22.val,upper_12_cell_23.val,upper_12_cell_24.val],
    ![upper_12_cell_03.val,upper_12_cell_13.val,upper_12_cell_23.val,upper_12_cell_33.val,upper_12_cell_34.val],
    ![upper_12_cell_04.val,upper_12_cell_14.val,upper_12_cell_24.val,upper_12_cell_34.val,upper_12_cell_44.val]]

private theorem upper_12_matrix_eq : smallCoefficient weightSeven 12=upper_12_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_12_cell_00.property
  · exact upper_12_cell_01.property
  · exact upper_12_cell_02.property
  · exact upper_12_cell_03.property
  · exact upper_12_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 12 1 0).trans upper_12_cell_01.property
  · exact upper_12_cell_11.property
  · exact upper_12_cell_12.property
  · exact upper_12_cell_13.property
  · exact upper_12_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 12 2 0).trans upper_12_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 12 2 1).trans upper_12_cell_12.property
  · exact upper_12_cell_22.property
  · exact upper_12_cell_23.property
  · exact upper_12_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 12 3 0).trans upper_12_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 12 3 1).trans upper_12_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 12 3 2).trans upper_12_cell_23.property
  · exact upper_12_cell_33.property
  · exact upper_12_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 12 4 0).trans upper_12_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 12 4 1).trans upper_12_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 12 4 2).trans upper_12_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 12 4 3).trans upper_12_cell_34.property
  · exact upper_12_cell_44.property

private theorem upper_12_first_pos : 0 < upper_12_matrix 0 0 := by
  dsimp only [upper_12_matrix,upper_12_cell_00,upper_12_cell_01,upper_12_cell_02,upper_12_cell_03,upper_12_cell_04,upper_12_cell_11,upper_12_cell_12,upper_12_cell_13,upper_12_cell_14,upper_12_cell_22,upper_12_cell_23,upper_12_cell_24,upper_12_cell_33,upper_12_cell_34,upper_12_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_12_delta_pos : 0 < delta upper_12_matrix := by
  dsimp only [upper_12_matrix,upper_12_cell_00,upper_12_cell_01,upper_12_cell_02,upper_12_cell_03,upper_12_cell_04,upper_12_cell_11,upper_12_cell_12,upper_12_cell_13,upper_12_cell_14,upper_12_cell_22,upper_12_cell_23,upper_12_cell_24,upper_12_cell_33,upper_12_cell_34,upper_12_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_12_schur_pos : 0 < schur upper_12_matrix 0 0 := by
  dsimp only [upper_12_matrix,upper_12_cell_00,upper_12_cell_01,upper_12_cell_02,upper_12_cell_03,upper_12_cell_04,upper_12_cell_11,upper_12_cell_12,upper_12_cell_13,upper_12_cell_14,upper_12_cell_22,upper_12_cell_23,upper_12_cell_24,upper_12_cell_33,upper_12_cell_34,upper_12_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_12_minor_pos : 0 < minor upper_12_matrix := by
  dsimp only [upper_12_matrix,upper_12_cell_00,upper_12_cell_01,upper_12_cell_02,upper_12_cell_03,upper_12_cell_04,upper_12_cell_11,upper_12_cell_12,upper_12_cell_13,upper_12_cell_14,upper_12_cell_22,upper_12_cell_23,upper_12_cell_24,upper_12_cell_33,upper_12_cell_34,upper_12_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_12_det_pos : 0 < determinant upper_12_matrix := by
  dsimp only [upper_12_matrix,upper_12_cell_00,upper_12_cell_01,upper_12_cell_02,upper_12_cell_03,upper_12_cell_04,upper_12_cell_11,upper_12_cell_12,upper_12_cell_13,upper_12_cell_14,upper_12_cell_22,upper_12_cell_23,upper_12_cell_24,upper_12_cell_33,upper_12_cell_34,upper_12_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_12_matrix_posDef : upper_12_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_12_first_pos upper_12_delta_pos upper_12_schur_pos
    upper_12_minor_pos upper_12_det_pos
  intro i j
  rw [← upper_12_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 12 i j

private theorem upper_12_posDef : (smallCoefficient weightSeven 12).PosDef := by
  rw [upper_12_matrix_eq]
  exact upper_12_matrix_posDef


private def upper_13_moment_0 : {v : ℝ // momentCoefficient weightSeven 13 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_13_moment_1 : {v : ℝ // momentCoefficient weightSeven 13 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_13_moment_2 : {v : ℝ // momentCoefficient weightSeven 13 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_13_moment_3 : {v : ℝ // momentCoefficient weightSeven 13 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_13_moment_4 : {v : ℝ // momentCoefficient weightSeven 13 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_13_moment_5 : {v : ℝ // momentCoefficient weightSeven 13 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_13_moment_6 : {v : ℝ // momentCoefficient weightSeven 13 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_13_moment_7 : {v : ℝ // momentCoefficient weightSeven 13 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_13_moment_8 : {v : ℝ // momentCoefficient weightSeven 13 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_13_cell_00 : {v : ℝ // smallCoefficient weightSeven 13 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_13_moment_0.property]
      dsimp only [upper_13_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_01 : {v : ℝ // smallCoefficient weightSeven 13 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_13_moment_0.property,upper_13_moment_1.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_02 : {v : ℝ // smallCoefficient weightSeven 13 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_03 : {v : ℝ // smallCoefficient weightSeven 13 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_04 : {v : ℝ // smallCoefficient weightSeven 13 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property,upper_13_moment_4.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3,upper_13_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_11 : {v : ℝ // smallCoefficient weightSeven 13 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_12 : {v : ℝ // smallCoefficient weightSeven 13 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_13 : {v : ℝ // smallCoefficient weightSeven 13 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property,upper_13_moment_4.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3,upper_13_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_14 : {v : ℝ // smallCoefficient weightSeven 13 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property,upper_13_moment_4.property,upper_13_moment_5.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3,upper_13_moment_4,upper_13_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_22 : {v : ℝ // smallCoefficient weightSeven 13 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property,upper_13_moment_4.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3,upper_13_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_23 : {v : ℝ // smallCoefficient weightSeven 13 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property,upper_13_moment_4.property,upper_13_moment_5.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3,upper_13_moment_4,upper_13_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_24 : {v : ℝ // smallCoefficient weightSeven 13 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property,upper_13_moment_4.property,upper_13_moment_5.property,upper_13_moment_6.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3,upper_13_moment_4,upper_13_moment_5,upper_13_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_33 : {v : ℝ // smallCoefficient weightSeven 13 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property,upper_13_moment_4.property,upper_13_moment_5.property,upper_13_moment_6.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3,upper_13_moment_4,upper_13_moment_5,upper_13_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_34 : {v : ℝ // smallCoefficient weightSeven 13 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property,upper_13_moment_4.property,upper_13_moment_5.property,upper_13_moment_6.property,upper_13_moment_7.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3,upper_13_moment_4,upper_13_moment_5,upper_13_moment_6,upper_13_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_cell_44 : {v : ℝ // smallCoefficient weightSeven 13 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_13_moment_0.property,upper_13_moment_1.property,upper_13_moment_2.property,upper_13_moment_3.property,upper_13_moment_4.property,upper_13_moment_5.property,upper_13_moment_6.property,upper_13_moment_7.property,upper_13_moment_8.property]
      dsimp only [upper_13_moment_0,upper_13_moment_1,upper_13_moment_2,upper_13_moment_3,upper_13_moment_4,upper_13_moment_5,upper_13_moment_6,upper_13_moment_7,upper_13_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_13_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_13_cell_00.val,upper_13_cell_01.val,upper_13_cell_02.val,upper_13_cell_03.val,upper_13_cell_04.val],
    ![upper_13_cell_01.val,upper_13_cell_11.val,upper_13_cell_12.val,upper_13_cell_13.val,upper_13_cell_14.val],
    ![upper_13_cell_02.val,upper_13_cell_12.val,upper_13_cell_22.val,upper_13_cell_23.val,upper_13_cell_24.val],
    ![upper_13_cell_03.val,upper_13_cell_13.val,upper_13_cell_23.val,upper_13_cell_33.val,upper_13_cell_34.val],
    ![upper_13_cell_04.val,upper_13_cell_14.val,upper_13_cell_24.val,upper_13_cell_34.val,upper_13_cell_44.val]]

private theorem upper_13_matrix_eq : smallCoefficient weightSeven 13=upper_13_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_13_cell_00.property
  · exact upper_13_cell_01.property
  · exact upper_13_cell_02.property
  · exact upper_13_cell_03.property
  · exact upper_13_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 13 1 0).trans upper_13_cell_01.property
  · exact upper_13_cell_11.property
  · exact upper_13_cell_12.property
  · exact upper_13_cell_13.property
  · exact upper_13_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 13 2 0).trans upper_13_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 13 2 1).trans upper_13_cell_12.property
  · exact upper_13_cell_22.property
  · exact upper_13_cell_23.property
  · exact upper_13_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 13 3 0).trans upper_13_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 13 3 1).trans upper_13_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 13 3 2).trans upper_13_cell_23.property
  · exact upper_13_cell_33.property
  · exact upper_13_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 13 4 0).trans upper_13_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 13 4 1).trans upper_13_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 13 4 2).trans upper_13_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 13 4 3).trans upper_13_cell_34.property
  · exact upper_13_cell_44.property

private theorem upper_13_first_pos : 0 < upper_13_matrix 0 0 := by
  dsimp only [upper_13_matrix,upper_13_cell_00,upper_13_cell_01,upper_13_cell_02,upper_13_cell_03,upper_13_cell_04,upper_13_cell_11,upper_13_cell_12,upper_13_cell_13,upper_13_cell_14,upper_13_cell_22,upper_13_cell_23,upper_13_cell_24,upper_13_cell_33,upper_13_cell_34,upper_13_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_13_delta_pos : 0 < delta upper_13_matrix := by
  dsimp only [upper_13_matrix,upper_13_cell_00,upper_13_cell_01,upper_13_cell_02,upper_13_cell_03,upper_13_cell_04,upper_13_cell_11,upper_13_cell_12,upper_13_cell_13,upper_13_cell_14,upper_13_cell_22,upper_13_cell_23,upper_13_cell_24,upper_13_cell_33,upper_13_cell_34,upper_13_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_13_schur_pos : 0 < schur upper_13_matrix 0 0 := by
  dsimp only [upper_13_matrix,upper_13_cell_00,upper_13_cell_01,upper_13_cell_02,upper_13_cell_03,upper_13_cell_04,upper_13_cell_11,upper_13_cell_12,upper_13_cell_13,upper_13_cell_14,upper_13_cell_22,upper_13_cell_23,upper_13_cell_24,upper_13_cell_33,upper_13_cell_34,upper_13_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_13_minor_pos : 0 < minor upper_13_matrix := by
  dsimp only [upper_13_matrix,upper_13_cell_00,upper_13_cell_01,upper_13_cell_02,upper_13_cell_03,upper_13_cell_04,upper_13_cell_11,upper_13_cell_12,upper_13_cell_13,upper_13_cell_14,upper_13_cell_22,upper_13_cell_23,upper_13_cell_24,upper_13_cell_33,upper_13_cell_34,upper_13_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_13_det_pos : 0 < determinant upper_13_matrix := by
  dsimp only [upper_13_matrix,upper_13_cell_00,upper_13_cell_01,upper_13_cell_02,upper_13_cell_03,upper_13_cell_04,upper_13_cell_11,upper_13_cell_12,upper_13_cell_13,upper_13_cell_14,upper_13_cell_22,upper_13_cell_23,upper_13_cell_24,upper_13_cell_33,upper_13_cell_34,upper_13_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_13_matrix_posDef : upper_13_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_13_first_pos upper_13_delta_pos upper_13_schur_pos
    upper_13_minor_pos upper_13_det_pos
  intro i j
  rw [← upper_13_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 13 i j

private theorem upper_13_posDef : (smallCoefficient weightSeven 13).PosDef := by
  rw [upper_13_matrix_eq]
  exact upper_13_matrix_posDef


private def upper_14_moment_0 : {v : ℝ // momentCoefficient weightSeven 14 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_14_moment_1 : {v : ℝ // momentCoefficient weightSeven 14 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_14_moment_2 : {v : ℝ // momentCoefficient weightSeven 14 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_14_moment_3 : {v : ℝ // momentCoefficient weightSeven 14 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_14_moment_4 : {v : ℝ // momentCoefficient weightSeven 14 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_14_moment_5 : {v : ℝ // momentCoefficient weightSeven 14 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_14_moment_6 : {v : ℝ // momentCoefficient weightSeven 14 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_14_moment_7 : {v : ℝ // momentCoefficient weightSeven 14 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_14_moment_8 : {v : ℝ // momentCoefficient weightSeven 14 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_14_cell_00 : {v : ℝ // smallCoefficient weightSeven 14 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_14_moment_0.property]
      dsimp only [upper_14_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_01 : {v : ℝ // smallCoefficient weightSeven 14 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_14_moment_0.property,upper_14_moment_1.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_02 : {v : ℝ // smallCoefficient weightSeven 14 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_03 : {v : ℝ // smallCoefficient weightSeven 14 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_04 : {v : ℝ // smallCoefficient weightSeven 14 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property,upper_14_moment_4.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3,upper_14_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_11 : {v : ℝ // smallCoefficient weightSeven 14 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_12 : {v : ℝ // smallCoefficient weightSeven 14 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_13 : {v : ℝ // smallCoefficient weightSeven 14 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property,upper_14_moment_4.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3,upper_14_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_14 : {v : ℝ // smallCoefficient weightSeven 14 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property,upper_14_moment_4.property,upper_14_moment_5.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3,upper_14_moment_4,upper_14_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_22 : {v : ℝ // smallCoefficient weightSeven 14 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property,upper_14_moment_4.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3,upper_14_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_23 : {v : ℝ // smallCoefficient weightSeven 14 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property,upper_14_moment_4.property,upper_14_moment_5.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3,upper_14_moment_4,upper_14_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_24 : {v : ℝ // smallCoefficient weightSeven 14 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property,upper_14_moment_4.property,upper_14_moment_5.property,upper_14_moment_6.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3,upper_14_moment_4,upper_14_moment_5,upper_14_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_33 : {v : ℝ // smallCoefficient weightSeven 14 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property,upper_14_moment_4.property,upper_14_moment_5.property,upper_14_moment_6.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3,upper_14_moment_4,upper_14_moment_5,upper_14_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_34 : {v : ℝ // smallCoefficient weightSeven 14 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property,upper_14_moment_4.property,upper_14_moment_5.property,upper_14_moment_6.property,upper_14_moment_7.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3,upper_14_moment_4,upper_14_moment_5,upper_14_moment_6,upper_14_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_cell_44 : {v : ℝ // smallCoefficient weightSeven 14 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_14_moment_0.property,upper_14_moment_1.property,upper_14_moment_2.property,upper_14_moment_3.property,upper_14_moment_4.property,upper_14_moment_5.property,upper_14_moment_6.property,upper_14_moment_7.property,upper_14_moment_8.property]
      dsimp only [upper_14_moment_0,upper_14_moment_1,upper_14_moment_2,upper_14_moment_3,upper_14_moment_4,upper_14_moment_5,upper_14_moment_6,upper_14_moment_7,upper_14_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_14_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_14_cell_00.val,upper_14_cell_01.val,upper_14_cell_02.val,upper_14_cell_03.val,upper_14_cell_04.val],
    ![upper_14_cell_01.val,upper_14_cell_11.val,upper_14_cell_12.val,upper_14_cell_13.val,upper_14_cell_14.val],
    ![upper_14_cell_02.val,upper_14_cell_12.val,upper_14_cell_22.val,upper_14_cell_23.val,upper_14_cell_24.val],
    ![upper_14_cell_03.val,upper_14_cell_13.val,upper_14_cell_23.val,upper_14_cell_33.val,upper_14_cell_34.val],
    ![upper_14_cell_04.val,upper_14_cell_14.val,upper_14_cell_24.val,upper_14_cell_34.val,upper_14_cell_44.val]]

private theorem upper_14_matrix_eq : smallCoefficient weightSeven 14=upper_14_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_14_cell_00.property
  · exact upper_14_cell_01.property
  · exact upper_14_cell_02.property
  · exact upper_14_cell_03.property
  · exact upper_14_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 14 1 0).trans upper_14_cell_01.property
  · exact upper_14_cell_11.property
  · exact upper_14_cell_12.property
  · exact upper_14_cell_13.property
  · exact upper_14_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 14 2 0).trans upper_14_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 14 2 1).trans upper_14_cell_12.property
  · exact upper_14_cell_22.property
  · exact upper_14_cell_23.property
  · exact upper_14_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 14 3 0).trans upper_14_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 14 3 1).trans upper_14_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 14 3 2).trans upper_14_cell_23.property
  · exact upper_14_cell_33.property
  · exact upper_14_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 14 4 0).trans upper_14_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 14 4 1).trans upper_14_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 14 4 2).trans upper_14_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 14 4 3).trans upper_14_cell_34.property
  · exact upper_14_cell_44.property

private theorem upper_14_first_pos : 0 < upper_14_matrix 0 0 := by
  dsimp only [upper_14_matrix,upper_14_cell_00,upper_14_cell_01,upper_14_cell_02,upper_14_cell_03,upper_14_cell_04,upper_14_cell_11,upper_14_cell_12,upper_14_cell_13,upper_14_cell_14,upper_14_cell_22,upper_14_cell_23,upper_14_cell_24,upper_14_cell_33,upper_14_cell_34,upper_14_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_14_delta_pos : 0 < delta upper_14_matrix := by
  dsimp only [upper_14_matrix,upper_14_cell_00,upper_14_cell_01,upper_14_cell_02,upper_14_cell_03,upper_14_cell_04,upper_14_cell_11,upper_14_cell_12,upper_14_cell_13,upper_14_cell_14,upper_14_cell_22,upper_14_cell_23,upper_14_cell_24,upper_14_cell_33,upper_14_cell_34,upper_14_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_14_schur_pos : 0 < schur upper_14_matrix 0 0 := by
  dsimp only [upper_14_matrix,upper_14_cell_00,upper_14_cell_01,upper_14_cell_02,upper_14_cell_03,upper_14_cell_04,upper_14_cell_11,upper_14_cell_12,upper_14_cell_13,upper_14_cell_14,upper_14_cell_22,upper_14_cell_23,upper_14_cell_24,upper_14_cell_33,upper_14_cell_34,upper_14_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_14_minor_pos : 0 < minor upper_14_matrix := by
  dsimp only [upper_14_matrix,upper_14_cell_00,upper_14_cell_01,upper_14_cell_02,upper_14_cell_03,upper_14_cell_04,upper_14_cell_11,upper_14_cell_12,upper_14_cell_13,upper_14_cell_14,upper_14_cell_22,upper_14_cell_23,upper_14_cell_24,upper_14_cell_33,upper_14_cell_34,upper_14_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_14_det_pos : 0 < determinant upper_14_matrix := by
  dsimp only [upper_14_matrix,upper_14_cell_00,upper_14_cell_01,upper_14_cell_02,upper_14_cell_03,upper_14_cell_04,upper_14_cell_11,upper_14_cell_12,upper_14_cell_13,upper_14_cell_14,upper_14_cell_22,upper_14_cell_23,upper_14_cell_24,upper_14_cell_33,upper_14_cell_34,upper_14_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_14_matrix_posDef : upper_14_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_14_first_pos upper_14_delta_pos upper_14_schur_pos
    upper_14_minor_pos upper_14_det_pos
  intro i j
  rw [← upper_14_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 14 i j

private theorem upper_14_posDef : (smallCoefficient weightSeven 14).PosDef := by
  rw [upper_14_matrix_eq]
  exact upper_14_matrix_posDef


private def upper_15_moment_0 : {v : ℝ // momentCoefficient weightSeven 15 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_15_moment_1 : {v : ℝ // momentCoefficient weightSeven 15 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_15_moment_2 : {v : ℝ // momentCoefficient weightSeven 15 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_15_moment_3 : {v : ℝ // momentCoefficient weightSeven 15 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_15_moment_4 : {v : ℝ // momentCoefficient weightSeven 15 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_15_moment_5 : {v : ℝ // momentCoefficient weightSeven 15 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_15_moment_6 : {v : ℝ // momentCoefficient weightSeven 15 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_15_moment_7 : {v : ℝ // momentCoefficient weightSeven 15 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_15_moment_8 : {v : ℝ // momentCoefficient weightSeven 15 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_15_cell_00 : {v : ℝ // smallCoefficient weightSeven 15 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_15_moment_0.property]
      dsimp only [upper_15_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_01 : {v : ℝ // smallCoefficient weightSeven 15 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_15_moment_0.property,upper_15_moment_1.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_02 : {v : ℝ // smallCoefficient weightSeven 15 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_03 : {v : ℝ // smallCoefficient weightSeven 15 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_04 : {v : ℝ // smallCoefficient weightSeven 15 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property,upper_15_moment_4.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3,upper_15_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_11 : {v : ℝ // smallCoefficient weightSeven 15 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_12 : {v : ℝ // smallCoefficient weightSeven 15 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_13 : {v : ℝ // smallCoefficient weightSeven 15 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property,upper_15_moment_4.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3,upper_15_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_14 : {v : ℝ // smallCoefficient weightSeven 15 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property,upper_15_moment_4.property,upper_15_moment_5.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3,upper_15_moment_4,upper_15_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_22 : {v : ℝ // smallCoefficient weightSeven 15 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property,upper_15_moment_4.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3,upper_15_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_23 : {v : ℝ // smallCoefficient weightSeven 15 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property,upper_15_moment_4.property,upper_15_moment_5.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3,upper_15_moment_4,upper_15_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_24 : {v : ℝ // smallCoefficient weightSeven 15 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property,upper_15_moment_4.property,upper_15_moment_5.property,upper_15_moment_6.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3,upper_15_moment_4,upper_15_moment_5,upper_15_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_33 : {v : ℝ // smallCoefficient weightSeven 15 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property,upper_15_moment_4.property,upper_15_moment_5.property,upper_15_moment_6.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3,upper_15_moment_4,upper_15_moment_5,upper_15_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_34 : {v : ℝ // smallCoefficient weightSeven 15 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property,upper_15_moment_4.property,upper_15_moment_5.property,upper_15_moment_6.property,upper_15_moment_7.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3,upper_15_moment_4,upper_15_moment_5,upper_15_moment_6,upper_15_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_cell_44 : {v : ℝ // smallCoefficient weightSeven 15 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_15_moment_0.property,upper_15_moment_1.property,upper_15_moment_2.property,upper_15_moment_3.property,upper_15_moment_4.property,upper_15_moment_5.property,upper_15_moment_6.property,upper_15_moment_7.property,upper_15_moment_8.property]
      dsimp only [upper_15_moment_0,upper_15_moment_1,upper_15_moment_2,upper_15_moment_3,upper_15_moment_4,upper_15_moment_5,upper_15_moment_6,upper_15_moment_7,upper_15_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_15_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_15_cell_00.val,upper_15_cell_01.val,upper_15_cell_02.val,upper_15_cell_03.val,upper_15_cell_04.val],
    ![upper_15_cell_01.val,upper_15_cell_11.val,upper_15_cell_12.val,upper_15_cell_13.val,upper_15_cell_14.val],
    ![upper_15_cell_02.val,upper_15_cell_12.val,upper_15_cell_22.val,upper_15_cell_23.val,upper_15_cell_24.val],
    ![upper_15_cell_03.val,upper_15_cell_13.val,upper_15_cell_23.val,upper_15_cell_33.val,upper_15_cell_34.val],
    ![upper_15_cell_04.val,upper_15_cell_14.val,upper_15_cell_24.val,upper_15_cell_34.val,upper_15_cell_44.val]]

private theorem upper_15_matrix_eq : smallCoefficient weightSeven 15=upper_15_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_15_cell_00.property
  · exact upper_15_cell_01.property
  · exact upper_15_cell_02.property
  · exact upper_15_cell_03.property
  · exact upper_15_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 15 1 0).trans upper_15_cell_01.property
  · exact upper_15_cell_11.property
  · exact upper_15_cell_12.property
  · exact upper_15_cell_13.property
  · exact upper_15_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 15 2 0).trans upper_15_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 15 2 1).trans upper_15_cell_12.property
  · exact upper_15_cell_22.property
  · exact upper_15_cell_23.property
  · exact upper_15_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 15 3 0).trans upper_15_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 15 3 1).trans upper_15_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 15 3 2).trans upper_15_cell_23.property
  · exact upper_15_cell_33.property
  · exact upper_15_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 15 4 0).trans upper_15_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 15 4 1).trans upper_15_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 15 4 2).trans upper_15_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 15 4 3).trans upper_15_cell_34.property
  · exact upper_15_cell_44.property

private theorem upper_15_first_pos : 0 < upper_15_matrix 0 0 := by
  dsimp only [upper_15_matrix,upper_15_cell_00,upper_15_cell_01,upper_15_cell_02,upper_15_cell_03,upper_15_cell_04,upper_15_cell_11,upper_15_cell_12,upper_15_cell_13,upper_15_cell_14,upper_15_cell_22,upper_15_cell_23,upper_15_cell_24,upper_15_cell_33,upper_15_cell_34,upper_15_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_15_delta_pos : 0 < delta upper_15_matrix := by
  dsimp only [upper_15_matrix,upper_15_cell_00,upper_15_cell_01,upper_15_cell_02,upper_15_cell_03,upper_15_cell_04,upper_15_cell_11,upper_15_cell_12,upper_15_cell_13,upper_15_cell_14,upper_15_cell_22,upper_15_cell_23,upper_15_cell_24,upper_15_cell_33,upper_15_cell_34,upper_15_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_15_schur_pos : 0 < schur upper_15_matrix 0 0 := by
  dsimp only [upper_15_matrix,upper_15_cell_00,upper_15_cell_01,upper_15_cell_02,upper_15_cell_03,upper_15_cell_04,upper_15_cell_11,upper_15_cell_12,upper_15_cell_13,upper_15_cell_14,upper_15_cell_22,upper_15_cell_23,upper_15_cell_24,upper_15_cell_33,upper_15_cell_34,upper_15_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_15_minor_pos : 0 < minor upper_15_matrix := by
  dsimp only [upper_15_matrix,upper_15_cell_00,upper_15_cell_01,upper_15_cell_02,upper_15_cell_03,upper_15_cell_04,upper_15_cell_11,upper_15_cell_12,upper_15_cell_13,upper_15_cell_14,upper_15_cell_22,upper_15_cell_23,upper_15_cell_24,upper_15_cell_33,upper_15_cell_34,upper_15_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_15_det_pos : 0 < determinant upper_15_matrix := by
  dsimp only [upper_15_matrix,upper_15_cell_00,upper_15_cell_01,upper_15_cell_02,upper_15_cell_03,upper_15_cell_04,upper_15_cell_11,upper_15_cell_12,upper_15_cell_13,upper_15_cell_14,upper_15_cell_22,upper_15_cell_23,upper_15_cell_24,upper_15_cell_33,upper_15_cell_34,upper_15_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_15_matrix_posDef : upper_15_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_15_first_pos upper_15_delta_pos upper_15_schur_pos
    upper_15_minor_pos upper_15_det_pos
  intro i j
  rw [← upper_15_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 15 i j

private theorem upper_15_posDef : (smallCoefficient weightSeven 15).PosDef := by
  rw [upper_15_matrix_eq]
  exact upper_15_matrix_posDef


private def upper_16_moment_0 : {v : ℝ // momentCoefficient weightSeven 16 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_16_moment_1 : {v : ℝ // momentCoefficient weightSeven 16 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_16_moment_2 : {v : ℝ // momentCoefficient weightSeven 16 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_16_moment_3 : {v : ℝ // momentCoefficient weightSeven 16 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_16_moment_4 : {v : ℝ // momentCoefficient weightSeven 16 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_16_moment_5 : {v : ℝ // momentCoefficient weightSeven 16 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_16_moment_6 : {v : ℝ // momentCoefficient weightSeven 16 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_16_moment_7 : {v : ℝ // momentCoefficient weightSeven 16 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_16_moment_8 : {v : ℝ // momentCoefficient weightSeven 16 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_16_cell_00 : {v : ℝ // smallCoefficient weightSeven 16 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_16_moment_0.property]
      dsimp only [upper_16_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_01 : {v : ℝ // smallCoefficient weightSeven 16 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_16_moment_0.property,upper_16_moment_1.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_02 : {v : ℝ // smallCoefficient weightSeven 16 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_03 : {v : ℝ // smallCoefficient weightSeven 16 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_04 : {v : ℝ // smallCoefficient weightSeven 16 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property,upper_16_moment_4.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3,upper_16_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_11 : {v : ℝ // smallCoefficient weightSeven 16 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_12 : {v : ℝ // smallCoefficient weightSeven 16 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_13 : {v : ℝ // smallCoefficient weightSeven 16 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property,upper_16_moment_4.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3,upper_16_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_14 : {v : ℝ // smallCoefficient weightSeven 16 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property,upper_16_moment_4.property,upper_16_moment_5.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3,upper_16_moment_4,upper_16_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_22 : {v : ℝ // smallCoefficient weightSeven 16 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property,upper_16_moment_4.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3,upper_16_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_23 : {v : ℝ // smallCoefficient weightSeven 16 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property,upper_16_moment_4.property,upper_16_moment_5.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3,upper_16_moment_4,upper_16_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_24 : {v : ℝ // smallCoefficient weightSeven 16 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property,upper_16_moment_4.property,upper_16_moment_5.property,upper_16_moment_6.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3,upper_16_moment_4,upper_16_moment_5,upper_16_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_33 : {v : ℝ // smallCoefficient weightSeven 16 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property,upper_16_moment_4.property,upper_16_moment_5.property,upper_16_moment_6.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3,upper_16_moment_4,upper_16_moment_5,upper_16_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_34 : {v : ℝ // smallCoefficient weightSeven 16 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property,upper_16_moment_4.property,upper_16_moment_5.property,upper_16_moment_6.property,upper_16_moment_7.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3,upper_16_moment_4,upper_16_moment_5,upper_16_moment_6,upper_16_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_cell_44 : {v : ℝ // smallCoefficient weightSeven 16 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_16_moment_0.property,upper_16_moment_1.property,upper_16_moment_2.property,upper_16_moment_3.property,upper_16_moment_4.property,upper_16_moment_5.property,upper_16_moment_6.property,upper_16_moment_7.property,upper_16_moment_8.property]
      dsimp only [upper_16_moment_0,upper_16_moment_1,upper_16_moment_2,upper_16_moment_3,upper_16_moment_4,upper_16_moment_5,upper_16_moment_6,upper_16_moment_7,upper_16_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_16_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_16_cell_00.val,upper_16_cell_01.val,upper_16_cell_02.val,upper_16_cell_03.val,upper_16_cell_04.val],
    ![upper_16_cell_01.val,upper_16_cell_11.val,upper_16_cell_12.val,upper_16_cell_13.val,upper_16_cell_14.val],
    ![upper_16_cell_02.val,upper_16_cell_12.val,upper_16_cell_22.val,upper_16_cell_23.val,upper_16_cell_24.val],
    ![upper_16_cell_03.val,upper_16_cell_13.val,upper_16_cell_23.val,upper_16_cell_33.val,upper_16_cell_34.val],
    ![upper_16_cell_04.val,upper_16_cell_14.val,upper_16_cell_24.val,upper_16_cell_34.val,upper_16_cell_44.val]]

private theorem upper_16_matrix_eq : smallCoefficient weightSeven 16=upper_16_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_16_cell_00.property
  · exact upper_16_cell_01.property
  · exact upper_16_cell_02.property
  · exact upper_16_cell_03.property
  · exact upper_16_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 16 1 0).trans upper_16_cell_01.property
  · exact upper_16_cell_11.property
  · exact upper_16_cell_12.property
  · exact upper_16_cell_13.property
  · exact upper_16_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 16 2 0).trans upper_16_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 16 2 1).trans upper_16_cell_12.property
  · exact upper_16_cell_22.property
  · exact upper_16_cell_23.property
  · exact upper_16_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 16 3 0).trans upper_16_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 16 3 1).trans upper_16_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 16 3 2).trans upper_16_cell_23.property
  · exact upper_16_cell_33.property
  · exact upper_16_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 16 4 0).trans upper_16_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 16 4 1).trans upper_16_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 16 4 2).trans upper_16_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 16 4 3).trans upper_16_cell_34.property
  · exact upper_16_cell_44.property

private theorem upper_16_first_pos : 0 < upper_16_matrix 0 0 := by
  dsimp only [upper_16_matrix,upper_16_cell_00,upper_16_cell_01,upper_16_cell_02,upper_16_cell_03,upper_16_cell_04,upper_16_cell_11,upper_16_cell_12,upper_16_cell_13,upper_16_cell_14,upper_16_cell_22,upper_16_cell_23,upper_16_cell_24,upper_16_cell_33,upper_16_cell_34,upper_16_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_16_delta_pos : 0 < delta upper_16_matrix := by
  dsimp only [upper_16_matrix,upper_16_cell_00,upper_16_cell_01,upper_16_cell_02,upper_16_cell_03,upper_16_cell_04,upper_16_cell_11,upper_16_cell_12,upper_16_cell_13,upper_16_cell_14,upper_16_cell_22,upper_16_cell_23,upper_16_cell_24,upper_16_cell_33,upper_16_cell_34,upper_16_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_16_schur_pos : 0 < schur upper_16_matrix 0 0 := by
  dsimp only [upper_16_matrix,upper_16_cell_00,upper_16_cell_01,upper_16_cell_02,upper_16_cell_03,upper_16_cell_04,upper_16_cell_11,upper_16_cell_12,upper_16_cell_13,upper_16_cell_14,upper_16_cell_22,upper_16_cell_23,upper_16_cell_24,upper_16_cell_33,upper_16_cell_34,upper_16_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_16_minor_pos : 0 < minor upper_16_matrix := by
  dsimp only [upper_16_matrix,upper_16_cell_00,upper_16_cell_01,upper_16_cell_02,upper_16_cell_03,upper_16_cell_04,upper_16_cell_11,upper_16_cell_12,upper_16_cell_13,upper_16_cell_14,upper_16_cell_22,upper_16_cell_23,upper_16_cell_24,upper_16_cell_33,upper_16_cell_34,upper_16_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_16_det_pos : 0 < determinant upper_16_matrix := by
  dsimp only [upper_16_matrix,upper_16_cell_00,upper_16_cell_01,upper_16_cell_02,upper_16_cell_03,upper_16_cell_04,upper_16_cell_11,upper_16_cell_12,upper_16_cell_13,upper_16_cell_14,upper_16_cell_22,upper_16_cell_23,upper_16_cell_24,upper_16_cell_33,upper_16_cell_34,upper_16_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_16_matrix_posDef : upper_16_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_16_first_pos upper_16_delta_pos upper_16_schur_pos
    upper_16_minor_pos upper_16_det_pos
  intro i j
  rw [← upper_16_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 16 i j

private theorem upper_16_posDef : (smallCoefficient weightSeven 16).PosDef := by
  rw [upper_16_matrix_eq]
  exact upper_16_matrix_posDef


private def upper_17_moment_0 : {v : ℝ // momentCoefficient weightSeven 17 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_17_moment_1 : {v : ℝ // momentCoefficient weightSeven 17 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_17_moment_2 : {v : ℝ // momentCoefficient weightSeven 17 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_17_moment_3 : {v : ℝ // momentCoefficient weightSeven 17 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_17_moment_4 : {v : ℝ // momentCoefficient weightSeven 17 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_17_moment_5 : {v : ℝ // momentCoefficient weightSeven 17 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_17_moment_6 : {v : ℝ // momentCoefficient weightSeven 17 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_17_moment_7 : {v : ℝ // momentCoefficient weightSeven 17 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_17_moment_8 : {v : ℝ // momentCoefficient weightSeven 17 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_17_cell_00 : {v : ℝ // smallCoefficient weightSeven 17 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_17_moment_0.property]
      dsimp only [upper_17_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_01 : {v : ℝ // smallCoefficient weightSeven 17 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_17_moment_0.property,upper_17_moment_1.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_02 : {v : ℝ // smallCoefficient weightSeven 17 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_03 : {v : ℝ // smallCoefficient weightSeven 17 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_04 : {v : ℝ // smallCoefficient weightSeven 17 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property,upper_17_moment_4.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3,upper_17_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_11 : {v : ℝ // smallCoefficient weightSeven 17 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_12 : {v : ℝ // smallCoefficient weightSeven 17 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_13 : {v : ℝ // smallCoefficient weightSeven 17 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property,upper_17_moment_4.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3,upper_17_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_14 : {v : ℝ // smallCoefficient weightSeven 17 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property,upper_17_moment_4.property,upper_17_moment_5.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3,upper_17_moment_4,upper_17_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_22 : {v : ℝ // smallCoefficient weightSeven 17 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property,upper_17_moment_4.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3,upper_17_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_23 : {v : ℝ // smallCoefficient weightSeven 17 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property,upper_17_moment_4.property,upper_17_moment_5.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3,upper_17_moment_4,upper_17_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_24 : {v : ℝ // smallCoefficient weightSeven 17 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property,upper_17_moment_4.property,upper_17_moment_5.property,upper_17_moment_6.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3,upper_17_moment_4,upper_17_moment_5,upper_17_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_33 : {v : ℝ // smallCoefficient weightSeven 17 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property,upper_17_moment_4.property,upper_17_moment_5.property,upper_17_moment_6.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3,upper_17_moment_4,upper_17_moment_5,upper_17_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_34 : {v : ℝ // smallCoefficient weightSeven 17 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property,upper_17_moment_4.property,upper_17_moment_5.property,upper_17_moment_6.property,upper_17_moment_7.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3,upper_17_moment_4,upper_17_moment_5,upper_17_moment_6,upper_17_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_cell_44 : {v : ℝ // smallCoefficient weightSeven 17 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_17_moment_0.property,upper_17_moment_1.property,upper_17_moment_2.property,upper_17_moment_3.property,upper_17_moment_4.property,upper_17_moment_5.property,upper_17_moment_6.property,upper_17_moment_7.property,upper_17_moment_8.property]
      dsimp only [upper_17_moment_0,upper_17_moment_1,upper_17_moment_2,upper_17_moment_3,upper_17_moment_4,upper_17_moment_5,upper_17_moment_6,upper_17_moment_7,upper_17_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_17_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_17_cell_00.val,upper_17_cell_01.val,upper_17_cell_02.val,upper_17_cell_03.val,upper_17_cell_04.val],
    ![upper_17_cell_01.val,upper_17_cell_11.val,upper_17_cell_12.val,upper_17_cell_13.val,upper_17_cell_14.val],
    ![upper_17_cell_02.val,upper_17_cell_12.val,upper_17_cell_22.val,upper_17_cell_23.val,upper_17_cell_24.val],
    ![upper_17_cell_03.val,upper_17_cell_13.val,upper_17_cell_23.val,upper_17_cell_33.val,upper_17_cell_34.val],
    ![upper_17_cell_04.val,upper_17_cell_14.val,upper_17_cell_24.val,upper_17_cell_34.val,upper_17_cell_44.val]]

private theorem upper_17_matrix_eq : smallCoefficient weightSeven 17=upper_17_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_17_cell_00.property
  · exact upper_17_cell_01.property
  · exact upper_17_cell_02.property
  · exact upper_17_cell_03.property
  · exact upper_17_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 17 1 0).trans upper_17_cell_01.property
  · exact upper_17_cell_11.property
  · exact upper_17_cell_12.property
  · exact upper_17_cell_13.property
  · exact upper_17_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 17 2 0).trans upper_17_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 17 2 1).trans upper_17_cell_12.property
  · exact upper_17_cell_22.property
  · exact upper_17_cell_23.property
  · exact upper_17_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 17 3 0).trans upper_17_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 17 3 1).trans upper_17_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 17 3 2).trans upper_17_cell_23.property
  · exact upper_17_cell_33.property
  · exact upper_17_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 17 4 0).trans upper_17_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 17 4 1).trans upper_17_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 17 4 2).trans upper_17_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 17 4 3).trans upper_17_cell_34.property
  · exact upper_17_cell_44.property

private theorem upper_17_first_pos : 0 < upper_17_matrix 0 0 := by
  dsimp only [upper_17_matrix,upper_17_cell_00,upper_17_cell_01,upper_17_cell_02,upper_17_cell_03,upper_17_cell_04,upper_17_cell_11,upper_17_cell_12,upper_17_cell_13,upper_17_cell_14,upper_17_cell_22,upper_17_cell_23,upper_17_cell_24,upper_17_cell_33,upper_17_cell_34,upper_17_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_17_delta_pos : 0 < delta upper_17_matrix := by
  dsimp only [upper_17_matrix,upper_17_cell_00,upper_17_cell_01,upper_17_cell_02,upper_17_cell_03,upper_17_cell_04,upper_17_cell_11,upper_17_cell_12,upper_17_cell_13,upper_17_cell_14,upper_17_cell_22,upper_17_cell_23,upper_17_cell_24,upper_17_cell_33,upper_17_cell_34,upper_17_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_17_schur_pos : 0 < schur upper_17_matrix 0 0 := by
  dsimp only [upper_17_matrix,upper_17_cell_00,upper_17_cell_01,upper_17_cell_02,upper_17_cell_03,upper_17_cell_04,upper_17_cell_11,upper_17_cell_12,upper_17_cell_13,upper_17_cell_14,upper_17_cell_22,upper_17_cell_23,upper_17_cell_24,upper_17_cell_33,upper_17_cell_34,upper_17_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_17_minor_pos : 0 < minor upper_17_matrix := by
  dsimp only [upper_17_matrix,upper_17_cell_00,upper_17_cell_01,upper_17_cell_02,upper_17_cell_03,upper_17_cell_04,upper_17_cell_11,upper_17_cell_12,upper_17_cell_13,upper_17_cell_14,upper_17_cell_22,upper_17_cell_23,upper_17_cell_24,upper_17_cell_33,upper_17_cell_34,upper_17_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_17_det_pos : 0 < determinant upper_17_matrix := by
  dsimp only [upper_17_matrix,upper_17_cell_00,upper_17_cell_01,upper_17_cell_02,upper_17_cell_03,upper_17_cell_04,upper_17_cell_11,upper_17_cell_12,upper_17_cell_13,upper_17_cell_14,upper_17_cell_22,upper_17_cell_23,upper_17_cell_24,upper_17_cell_33,upper_17_cell_34,upper_17_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_17_matrix_posDef : upper_17_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_17_first_pos upper_17_delta_pos upper_17_schur_pos
    upper_17_minor_pos upper_17_det_pos
  intro i j
  rw [← upper_17_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 17 i j

private theorem upper_17_posDef : (smallCoefficient weightSeven 17).PosDef := by
  rw [upper_17_matrix_eq]
  exact upper_17_matrix_posDef


private def upper_18_moment_0 : {v : ℝ // momentCoefficient weightSeven 18 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_18_moment_1 : {v : ℝ // momentCoefficient weightSeven 18 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_18_moment_2 : {v : ℝ // momentCoefficient weightSeven 18 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_18_moment_3 : {v : ℝ // momentCoefficient weightSeven 18 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_18_moment_4 : {v : ℝ // momentCoefficient weightSeven 18 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_18_moment_5 : {v : ℝ // momentCoefficient weightSeven 18 5=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_18_moment_6 : {v : ℝ // momentCoefficient weightSeven 18 6=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_18_moment_7 : {v : ℝ // momentCoefficient weightSeven 18 7=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_18_moment_8 : {v : ℝ // momentCoefficient weightSeven 18 8=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs => norm_num [momentCoefficient,rCoefficient,bCoefficient,pick,weightSeven,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]

private def upper_18_cell_00 : {v : ℝ // smallCoefficient weightSeven 18 0 0=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e00,upper_18_moment_0.property]
      dsimp only [upper_18_moment_0]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_01 : {v : ℝ // smallCoefficient weightSeven 18 0 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e01,upper_18_moment_0.property,upper_18_moment_1.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_02 : {v : ℝ // smallCoefficient weightSeven 18 0 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e02,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_03 : {v : ℝ // smallCoefficient weightSeven 18 0 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e03,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_04 : {v : ℝ // smallCoefficient weightSeven 18 0 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e04,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property,upper_18_moment_4.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3,upper_18_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_11 : {v : ℝ // smallCoefficient weightSeven 18 1 1=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e11,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_12 : {v : ℝ // smallCoefficient weightSeven 18 1 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e12,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_13 : {v : ℝ // smallCoefficient weightSeven 18 1 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e13,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property,upper_18_moment_4.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3,upper_18_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_14 : {v : ℝ // smallCoefficient weightSeven 18 1 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e14,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property,upper_18_moment_4.property,upper_18_moment_5.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3,upper_18_moment_4,upper_18_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_22 : {v : ℝ // smallCoefficient weightSeven 18 2 2=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e22,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property,upper_18_moment_4.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3,upper_18_moment_4]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_23 : {v : ℝ // smallCoefficient weightSeven 18 2 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e23,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property,upper_18_moment_4.property,upper_18_moment_5.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3,upper_18_moment_4,upper_18_moment_5]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_24 : {v : ℝ // smallCoefficient weightSeven 18 2 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e24,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property,upper_18_moment_4.property,upper_18_moment_5.property,upper_18_moment_6.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3,upper_18_moment_4,upper_18_moment_5,upper_18_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_33 : {v : ℝ // smallCoefficient weightSeven 18 3 3=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e33,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property,upper_18_moment_4.property,upper_18_moment_5.property,upper_18_moment_6.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3,upper_18_moment_4,upper_18_moment_5,upper_18_moment_6]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_34 : {v : ℝ // smallCoefficient weightSeven 18 3 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e34,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property,upper_18_moment_4.property,upper_18_moment_5.property,upper_18_moment_6.property,upper_18_moment_7.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3,upper_18_moment_4,upper_18_moment_5,upper_18_moment_6,upper_18_moment_7]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_cell_44 : {v : ℝ // smallCoefficient weightSeven 18 4 4=v} := by
  refine ⟨?value,?certificate⟩
  case certificate =>
    conv_lhs =>
      simp only [smallCoefficient,entryPoly,e44,upper_18_moment_0.property,upper_18_moment_1.property,upper_18_moment_2.property,upper_18_moment_3.property,upper_18_moment_4.property,upper_18_moment_5.property,upper_18_moment_6.property,upper_18_moment_7.property,upper_18_moment_8.property]
      dsimp only [upper_18_moment_0,upper_18_moment_1,upper_18_moment_2,upper_18_moment_3,upper_18_moment_4,upper_18_moment_5,upper_18_moment_6,upper_18_moment_7,upper_18_moment_8]
      norm_num [loadCoefficient,rowZero,rowOne,Fin.sum_univ_succ,
        Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two,Matrix.cons_val_succ,Fin.ext_iff]
      norm_num [pick,Nat.choose_eq_descFactorial_div_factorial,Nat.descFactorial,Nat.factorial]
      norm_num [paidSevenSchur_00,paidSevenSchur_01,paidSevenSchur_11]

private def upper_18_matrix : Matrix (Fin 5) (Fin 5) ℝ :=
  ![![upper_18_cell_00.val,upper_18_cell_01.val,upper_18_cell_02.val,upper_18_cell_03.val,upper_18_cell_04.val],
    ![upper_18_cell_01.val,upper_18_cell_11.val,upper_18_cell_12.val,upper_18_cell_13.val,upper_18_cell_14.val],
    ![upper_18_cell_02.val,upper_18_cell_12.val,upper_18_cell_22.val,upper_18_cell_23.val,upper_18_cell_24.val],
    ![upper_18_cell_03.val,upper_18_cell_13.val,upper_18_cell_23.val,upper_18_cell_33.val,upper_18_cell_34.val],
    ![upper_18_cell_04.val,upper_18_cell_14.val,upper_18_cell_24.val,upper_18_cell_34.val,upper_18_cell_44.val]]

private theorem upper_18_matrix_eq : smallCoefficient weightSeven 18=upper_18_matrix := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact upper_18_cell_00.property
  · exact upper_18_cell_01.property
  · exact upper_18_cell_02.property
  · exact upper_18_cell_03.property
  · exact upper_18_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 18 1 0).trans upper_18_cell_01.property
  · exact upper_18_cell_11.property
  · exact upper_18_cell_12.property
  · exact upper_18_cell_13.property
  · exact upper_18_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 18 2 0).trans upper_18_cell_02.property
  · exact (smallCoefficient_symmetric weightSeven 18 2 1).trans upper_18_cell_12.property
  · exact upper_18_cell_22.property
  · exact upper_18_cell_23.property
  · exact upper_18_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 18 3 0).trans upper_18_cell_03.property
  · exact (smallCoefficient_symmetric weightSeven 18 3 1).trans upper_18_cell_13.property
  · exact (smallCoefficient_symmetric weightSeven 18 3 2).trans upper_18_cell_23.property
  · exact upper_18_cell_33.property
  · exact upper_18_cell_34.property
  · exact (smallCoefficient_symmetric weightSeven 18 4 0).trans upper_18_cell_04.property
  · exact (smallCoefficient_symmetric weightSeven 18 4 1).trans upper_18_cell_14.property
  · exact (smallCoefficient_symmetric weightSeven 18 4 2).trans upper_18_cell_24.property
  · exact (smallCoefficient_symmetric weightSeven 18 4 3).trans upper_18_cell_34.property
  · exact upper_18_cell_44.property

private theorem upper_18_first_pos : 0 < upper_18_matrix 0 0 := by
  dsimp only [upper_18_matrix,upper_18_cell_00,upper_18_cell_01,upper_18_cell_02,upper_18_cell_03,upper_18_cell_04,upper_18_cell_11,upper_18_cell_12,upper_18_cell_13,upper_18_cell_14,upper_18_cell_22,upper_18_cell_23,upper_18_cell_24,upper_18_cell_33,upper_18_cell_34,upper_18_cell_44]
  simp only [Matrix.cons_val_zero]
  norm_num1

private theorem upper_18_delta_pos : 0 < delta upper_18_matrix := by
  dsimp only [upper_18_matrix,upper_18_cell_00,upper_18_cell_01,upper_18_cell_02,upper_18_cell_03,upper_18_cell_04,upper_18_cell_11,upper_18_cell_12,upper_18_cell_13,upper_18_cell_14,upper_18_cell_22,upper_18_cell_23,upper_18_cell_24,upper_18_cell_33,upper_18_cell_34,upper_18_cell_44]
  simp only [delta,Matrix.cons_val_zero,Matrix.cons_val_one]
  norm_num1

private theorem upper_18_schur_pos : 0 < schur upper_18_matrix 0 0 := by
  dsimp only [upper_18_matrix,upper_18_cell_00,upper_18_cell_01,upper_18_cell_02,upper_18_cell_03,upper_18_cell_04,upper_18_cell_11,upper_18_cell_12,upper_18_cell_13,upper_18_cell_14,upper_18_cell_22,upper_18_cell_23,upper_18_cell_24,upper_18_cell_33,upper_18_cell_34,upper_18_cell_44]
  simp only [schur,delta,tailIndex_zero,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two]
  norm_num1

private theorem upper_18_minor_pos : 0 < minor upper_18_matrix := by
  dsimp only [upper_18_matrix,upper_18_cell_00,upper_18_cell_01,upper_18_cell_02,upper_18_cell_03,upper_18_cell_04,upper_18_cell_11,upper_18_cell_12,upper_18_cell_13,upper_18_cell_14,upper_18_cell_22,upper_18_cell_23,upper_18_cell_24,upper_18_cell_33,upper_18_cell_34,upper_18_cell_44]
  simp only [minor,schur,delta,tailIndex_zero,tailIndex_one,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons4_two]
  norm_num1

private theorem upper_18_det_pos : 0 < determinant upper_18_matrix := by
  dsimp only [upper_18_matrix,upper_18_cell_00,upper_18_cell_01,upper_18_cell_02,upper_18_cell_03,upper_18_cell_04,upper_18_cell_11,upper_18_cell_12,upper_18_cell_13,upper_18_cell_14,upper_18_cell_22,upper_18_cell_23,upper_18_cell_24,upper_18_cell_33,upper_18_cell_34,upper_18_cell_44]
  simp only [determinant,minor,schur,delta,tailIndex_zero,tailIndex_one,tailIndex_two,Matrix.cons_val_zero,Matrix.cons_val_one,cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  norm_num1

private theorem upper_18_matrix_posDef : upper_18_matrix.PosDef := by
  apply posDef_of_schur_signs ?_ upper_18_first_pos upper_18_delta_pos upper_18_schur_pos
    upper_18_minor_pos upper_18_det_pos
  intro i j
  rw [← upper_18_matrix_eq]
  exact smallCoefficient_symmetric weightSeven 18 i j

private theorem upper_18_posDef : (smallCoefficient weightSeven 18).PosDef := by
  rw [upper_18_matrix_eq]
  exact upper_18_matrix_posDef


private theorem zero_coefficient_posDef (n : Fin 26) :
    (fastCoefficient 0 n.val).PosDef := by
  rw [fast_small]
  fin_cases n
  · exact zero_0_posDef
  · exact zero_1_posDef
  · exact zero_2_posDef
  · exact zero_3_posDef
  · exact zero_4_posDef
  · exact zero_5_posDef
  · exact zero_6_posDef
  · exact zero_7_posDef
  · exact zero_8_posDef
  · exact zero_9_posDef
  · exact zero_10_posDef
  · exact zero_11_posDef
  · exact zero_12_posDef
  · exact zero_13_posDef
  · exact zero_14_posDef
  · exact zero_15_posDef
  · exact zero_16_posDef
  · exact zero_17_posDef
  · exact zero_18_posDef
  · exact zero_19_posDef
  · exact zero_20_posDef
  · exact zero_21_posDef
  · exact zero_22_posDef
  · exact zero_23_posDef
  · exact zero_24_posDef
  · exact zero_25_posDef

private theorem upper_low_coefficient_posDef (n : Fin 19) :
    (fastCoefficient weightSeven n.val).PosDef := by
  rw [fast_small]
  fin_cases n
  · exact upper_0_posDef
  · exact upper_1_posDef
  · exact upper_2_posDef
  · exact upper_3_posDef
  · exact upper_4_posDef
  · exact upper_5_posDef
  · exact upper_6_posDef
  · exact upper_7_posDef
  · exact upper_8_posDef
  · exact upper_9_posDef
  · exact upper_10_posDef
  · exact upper_11_posDef
  · exact upper_12_posDef
  · exact upper_13_posDef
  · exact upper_14_posDef
  · exact upper_15_posDef
  · exact upper_16_posDef
  · exact upper_17_posDef
  · exact upper_18_posDef
private theorem upper_coefficient_posDef (n : Fin 26) :
    (fastCoefficient weightSeven n.val).PosDef := by
  by_cases hn : 19 ≤ n.val
  · rw [coefficient_weight_independent weightSeven n.val hn]
    exact zero_coefficient_posDef n
  · exact upper_low_coefficient_posDef ⟨n.val,by omega⟩
private theorem coefficient_posDef {z : ℝ} (hz : 0 ≤ z) (hw : z ≤ weightSeven)
    (n : Fin 26) : (fastCoefficient z n.val).PosDef := by
  by_cases he : z = weightSeven
  · subst z
    exact upper_coefficient_posDef n
  have ht : 0 < weightSeven-z := sub_pos.mpr (lt_of_le_of_ne hw he)
  have hscaled : (weightSeven • fastCoefficient z n.val).PosDef := by
    rw [coefficient_affine]
    exact ((zero_coefficient_posDef n).smul ht).add_posSemidef
      ((upper_coefficient_posDef n).posSemidef.smul hz)
  have hweight : 0 < weightSeven := by norm_num [weightSeven]
  have hback := hscaled.smul (inv_pos.mpr hweight)
  simpa only [smul_smul,inv_mul_cancel₀ hweight.ne',one_smul] using hback

private def matrixPolynomial (z u : ℝ) : Matrix (Fin 5) (Fin 5) ℝ :=
  ∑ n : Fin 26, u^n.val • fastCoefficient z n.val

private theorem matrixPolynomial_posDef {z u : ℝ}
    (hz : 0 ≤ z) (hw : z ≤ weightSeven) (hu : 0 ≤ u) :
    (matrixPolynomial z u).PosDef := by
  unfold matrixPolynomial
  rw [Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_smul]
  exact (coefficient_posDef hz hw 0).add_posSemidef
    (Matrix.posSemidef_sum _ fun n _ =>
      ((coefficient_posDef hz hw n.succ).posSemidef.smul (pow_nonneg hu _)))

open scoped EightCrossData

private theorem radial_eval (p : ℝ[X]) (u : ℝ) (k : ℕ) (hk : k ≤ 8) :
    (radial p k).eval u = rMoment (p.eval u) k := by
  interval_cases k <;>
    norm_num [radial,rp0,rp1,rp2,rp3,rp4,rp5,rp6,rp7,rp8] <;>
    norm_cross_model

private theorem mixed_eval (p : ℝ[X]) (u : ℝ) (k : ℕ) (hk : k ≤ 8) :
    (mixed p k).eval u = bMoment (p.eval u) k := by
  interval_cases k <;>
    norm_num [mixed,bp0,bp1,bp2,bp3,bp4,bp5,bp6,bp7,bp8] <;>
    norm_cross_model

private theorem moment_eval (z u : ℝ) (k : ℕ) (hk : k ≤ 8) :
    (moment z k).eval u = ((7:ℝ)^k)⁻¹ *
      ((u+1)^(23-k)*rMoment (7*(u+1)) k+
        8*z*((u+1)^(8-k)*bMoment (7*(u+1)) k)) := by
  simp only [moment,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_add,
    Polynomial.eval_pow,radial_eval scale u k hk,mixed_eval scale u k hk]
  norm_num [scale,factor]

private theorem moment_eval_scaled (z u : ℝ) (k : ℕ) (hk : k ≤ 8)
    (hu : u+1 ≠ 0) :
    (moment z k).eval u = (u+1)^23 *
      ((rMoment (7*(u+1)) k+8*(z/(u+1)^15)*bMoment (7*(u+1)) k)/
        (7*(u+1))^k) := by
  rw [moment_eval z u k hk,pow_sub₀ (u+1) hu (by omega : k ≤ 23),
    pow_sub₀ (u+1) hu hk]
  simp only [mul_pow]
  field_simp [hu]

private theorem rayPolynomial_degree (z : ℝ) (i j : Fin 5) :
    (rayPolynomial z i j).natDegree ≤ 25 := by
  apply Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro n hn
  change coefficient z n i j = 0
  rw [coefficient_eq,fastCoefficient_eq_zero z n hn,Matrix.zero_apply]

private theorem rayPolynomial_eval (z u : ℝ) (i j : Fin 5) :
    (rayPolynomial z i j).eval u = matrixPolynomial z u i j := by
  rw [Polynomial.eval_eq_sum_range'
    (lt_of_le_of_lt (rayPolynomial_degree z i j) (by norm_num : 25 < 26)) u,
    ← Fin.sum_univ_eq_sum_range]
  simp only [matrixPolynomial,Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro n _
  change coefficient z n.val i j*u^n.val = u^n.val*fastCoefficient z n.val i j
  rw [coefficient_eq]
  ring
open FifthNativeRay

private theorem leadingMatrix_moments (q z : ℝ) : leadingMatrix q z =
    (fun i j : Fin 5 => (rMoment q (i.val+j.val)+8*z*bMoment q (i.val+j.val))/
      q^(i.val+j.val) : Matrix (Fin 5) (Fin 5) ℝ) := by
  ext i j
  simp only [leadingMatrix,leadingMoment]
  rw [EightCrossData.radial_eq q (i.val+j.val) (by omega),
    EightCrossData.mixed_eq q (i.val+j.val) (by omega)]

private theorem load_zero_entry (q : ℝ) (j : Fin 5) :
    (loadMap*nativeBasis q) 0 j =
      gaussianBasis j 2/q^2+420*(gaussianBasis j 3/q^3) := by
  norm_num [loadMap,nativeBasis,Matrix.mul_apply,Fin.sum_univ_succ]
  rfl

private theorem load_one_entry (q : ℝ) (j : Fin 5) :
    (loadMap*nativeBasis q) 1 j =
      gaussianBasis j 3/q^3+1568*(gaussianBasis j 4/q^4) := by
  norm_num [loadMap,nativeBasis,Matrix.mul_apply,Fin.sum_univ_succ]
  rfl

private theorem row0_eval (u : ℝ) (hu : u+1 ≠ 0) (j : Fin 5) :
    (row0 j).eval u = 49*(u+1)^4*(loadMap*nativeBasis (7*(u+1))) 0 j := by
  rw [load_zero_entry]
  fin_cases j <;>
    norm_num [row0,factor,gaussianBasis,Matrix.cons_val_zero,Matrix.cons_val_one,
      cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  all_goals field_simp [hu]
  all_goals ring

private theorem row1_eval (u : ℝ) (hu : u+1 ≠ 0) (j : Fin 5) :
    (row1 j).eval u = 49*(u+1)^4*(loadMap*nativeBasis (7*(u+1))) 1 j := by
  rw [load_one_entry]
  fin_cases j <;>
    norm_num [row1,factor,gaussianBasis,Matrix.cons_val_zero,Matrix.cons_val_one,
      cons5_two,cons5_three,cons5_four,cons4_two,cons4_three,cons3_two]
  all_goals field_simp [hu]
  all_goals ring

private theorem paid_symmetry : paidSevenSchur 1 0 = paidSevenSchur 0 1 := by
  have h := congrFun (congrFun crossCoefficient_posDef.isHermitian 0) 1
  simpa only [Matrix.conjTranspose_apply,star_trivial] using h

private theorem loadPolynomial_eval (u : ℝ) (hu : u+1 ≠ 0) (i j : Fin 5) :
    (loadPolynomial i j).eval u = (u+1)^23*(7*(u+1))^4*
      loadGram (7*(u+1)) i j := by
  simp only [loadPolynomial,Polynomial.eval_mul,Polynomial.eval_add,
    Polynomial.eval_pow,Polynomial.eval_C,row0_eval u hu,row1_eval u hu]
  have he : factor.eval u = u+1 := by simp [factor]
  rw [he]
  change _ = (u+1)^23*(7*(u+1))^4*
    (∑ a : Fin 2, (∑ b : Fin 2,
      star ((loadMap*nativeBasis (7*(u+1))) b i)*paidSevenSchur b a)*
        (loadMap*nativeBasis (7*(u+1))) a j)
  simp only [Fin.sum_univ_two,star_trivial,paid_symmetry]
  ring

private theorem matrixPolynomial_model (z u : ℝ) (hu : u+1 ≠ 0) :
    matrixPolynomial z u = (u+1)^23 •
      (gaussianGram (leadingMatrix (7*(u+1)) (z/(u+1)^15))-
        ((3/20)*(7*(u+1))^4) • loadGram (7*(u+1))-
        (147/4000 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)) := by
  ext i j
  rw [← rayPolynomial_eval]
  have hm (a b : Fin 5) := moment_eval_scaled z u (a.val+b.val) (by omega) hu
  have hs : (∑ a : Fin 5, ∑ b : Fin 5,
      C (gaussianBasis i a*gaussianBasis j b)*moment z (a.val+b.val)).eval u =
      (u+1)^23*gaussianGram
        (leadingMatrix (7*(u+1)) (z/(u+1)^15)) i j := by
    simp only [Polynomial.eval_finsetSum,Polynomial.eval_mul,Polynomial.eval_C,
      hm,gaussianGram,leadingMatrix_moments,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  have hd : (if i=j then C (147/4000)*factor^23 else (0:ℝ[X])).eval u =
      (u+1)^23*((147/4000 : ℝ)*(1 : Matrix (Fin 5) (Fin 5) ℝ) i j) := by
    by_cases hij : i=j <;> simp [hij,factor,Matrix.one_apply]
    ring
  simp only [rayPolynomial,Polynomial.eval_sub,hs,hd,
    Polynomial.eval_mul,Polynomial.eval_C,loadPolynomial_eval u hu,
    Matrix.smul_apply,smul_eq_mul,Matrix.sub_apply]
  ring



/-- The retained Gaussian pair pays the quartic load and a complete-source error reserve. -/
theorem model_quartic_reserve_from_seven_posDef {q : ℝ} (hq : 7 ≤ q) :
    (gaussianGram (leadingMatrix q (Real.exp (-3*q)))-
      ((3/20)*q^4) • loadGram q-
      (147/4000 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)).PosDef := by
  have hu : 0 ≤ q/7-1 := by linarith only [hq]
  have hf : 0 < (q/7-1)+1 := by linarith only [hq]
  have hw := rescaled_weight_bounds hq
  have h := matrixPolynomial_posDef hw.1 hw.2 hu
  rw [matrixPolynomial_model _ _ hf.ne'] at h
  have hqeq : 7*(q/7-1+1)=q := by ring
  have hzeq : Real.exp (-3*q)*(q/7)^15/(q/7-1+1)^15 = Real.exp (-3*q) := by
    have he : q/7-1+1=q/7 := by ring
    rw [he]
    exact mul_div_cancel_right₀ _ (pow_ne_zero _ (by linarith only [hq] : q/7 ≠ 0))
  rw [hqeq,hzeq] at h
  have hback := h.smul (inv_pos.mpr (pow_pos hf 23))
  simpa only [smul_smul,inv_mul_cancel₀ (pow_pos hf 23).ne',one_smul] using hback


/-- The scale-eight reserve follows from the scale-seven ray. -/
theorem model_quartic_reserve_posDef {q : ℝ} (hq : 8 ≤ q) :
    (gaussianGram (leadingMatrix q (Real.exp (-3*q)))-
      ((3/20)*q^4) • loadGram q-
      (147/4000 : ℝ) • (1 : Matrix (Fin 5) (Fin 5) ℝ)).PosDef :=
  model_quartic_reserve_from_seven_posDef (by linarith only [hq])


end GaloisForLFunctions.ThetaCuspSections.QuarticRayCertificate
