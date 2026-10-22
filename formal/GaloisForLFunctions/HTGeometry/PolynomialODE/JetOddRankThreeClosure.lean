import GaloisForLFunctions.HTGeometry.PolynomialODE.JetRankThreeClosure
import GaloisForLFunctions.HTGeometry.PolynomialODE.SeamJetOrderValues

/-!
# Odd rank-three theta seam closure

Exact elimination through the twelfth modular mass derivative gives the odd
rank-three reflected Hankel determinant. Its polynomial is strictly negative
on the proved self-dual source interval. All identities are symbolic ring proofs.
-/

open scoped BigOperators ContDiff
namespace HTGeometry
noncomputable section

/-- Modular polynomial for the signed odd rank-three reflected seam. -/
def modularThetaReflectedTenthSeamPolynomial {K : Type*} [Field K] (X : K) : K :=
    (16275380625 / 512) +
    (-142861674375 / 512) * X ^ (1 : ℕ) +
    (47752328428875 / 65536) * X ^ (2 : ℕ) +
    (-202162197691125 / 262144) * X ^ (3 : ℕ) +
    (359654516607375 / 1048576) * X ^ (4 : ℕ) +
    (-312458771094525 / 4194304) * X ^ (5 : ℕ) +
    (277466964716925 / 16777216) * X ^ (6 : ℕ) +
    (-289890788929155 / 67108864) * X ^ (7 : ℕ) +
    (65149999997625 / 268435456) * X ^ (8 : ℕ) +
    (-5811676667055 / 1073741824) * X ^ (9 : ℕ) +
    (1347619807251 / 1073741824) * X ^ (10 : ℕ) +
    (-86414468409 / 4294967296) * X ^ (11 : ℕ) +
    (34486304985 / 17179869184) * X ^ (12 : ℕ) +
    (-4788287325 / 17179869184) * X ^ (13 : ℕ) +
    (-374144625 / 137438953472) * X ^ (14 : ℕ) +
    (64029375 / 549755813888) * X ^ (15 : ℕ)

/-- Exact twelfth-jet elimination for the odd rank-three reflection block. -/
theorem modularThetaReflectedTenthSeamJetElimination
    (M R : ℂ) (h z r p : ℕ → ℂ)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh : ∀ n, h (n + 1) =
      -(1 / 6 : ℂ) *
        scalarJetConvolution h
          (fun k => p k + scalarJetConvolution r z k) n)
    (hz : ∀ n, z (n + 1) =
      -scalarJetConvolution r
        (fun k => scalarJetUnit k - scalarJetConvolution z z k) n)
    (hr : ∀ n, r (n + 1) =
      -(2 / 3 : ℂ) *
        scalarJetConvolution r
          (fun k => p k + scalarJetConvolution r z k) n)
    (hp : ∀ n, p (n + 1) =
      3 * scalarJetUnit n -
        (1 / 3 : ℂ) * scalarJetConvolution p p n +
        (1 / 12 : ℂ) *
          scalarJetConvolution (scalarJetConvolution r r)
            (fun k => 3 * scalarJetUnit k +
              scalarJetConvolution z z k) n) :
    let f : ℕ → ℂ :=
      fun n => (h (n + 2) - (1 / 4 : ℂ) * h n) / 2
    signedEvenHankelThreeDetC
      (-2 * f 0 * f 2)
      (2 * f 0 * f 4 + 6 * f 2 ^ (2 : ℕ))
      (-2 * f 0 * f 6 - 30 * f 2 * f 4)
      (2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ (2 : ℕ))
      (-2 * f 0 * f 10 - 90 * f 2 * f 8 - 420 * f 4 * f 6) =
      M ^ (6 : ℕ) * modularThetaReflectedTenthSeamPolynomial (R ^ (2 : ℕ)) := by
  have J : SeamJetSystem M R h z r p :=
    ⟨hh0, hz0, hr0, hp0, hh, hz, hr, hp⟩
  have hh2 := seamJetH2 J
  have hh4 := seamJetH4 J
  have hh6 := seamJetH6 J
  have hh8 := seamJetH8 J
  have hh10 := seamJetH10 J
  have hh12 := seamJetH12 J
  let f : ℕ → ℂ := fun n => (h (n+2)-(1/4:ℂ)*h n)/2
  let p0 (X : ℂ) : ℂ := (45 / 64) + (-165 / 256)*X^(1 : ℕ) + (21 / 256)*X^(2 : ℕ) + (1 / 1024)*X^(3 : ℕ)
  have he0 : -2 * f 0 * f 2 = M^(2 : ℕ)*p0 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4]
    dsimp [p0]
    ring
  let p1 (X : ℂ) : ℂ := (765 / 64) + (-2505 / 128)*X^(1 : ℕ) + (4461 / 1024)*X^(2 : ℕ) + (77 / 1024)*X^(3 : ℕ) + (27 / 4096)*X^(4 : ℕ)
  have he1 : 2 * f 0 * f 4 + 6 * f 2 ^ (2 : ℕ) = M^(2 : ℕ)*p1 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4, hh6]
    dsimp [p1]
    ring
  let p2 (X : ℂ) : ℂ := (24345 / 64) + (-243615 / 256)*X^(1 : ℕ) + (333759 / 1024)*X^(2 : ℕ) + (31519 / 4096)*X^(3 : ℕ) + (8199 / 4096)*X^(4 : ℕ) + (-21 / 16384)*X^(5 : ℕ)
  have he2 : -2 * f 0 * f 6 - 30 * f 2 * f 4 = M^(2 : ℕ)*p2 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4, hh6, hh8]
    dsimp [p2]
    ring
  let p3 (X : ℂ) : ℂ := (1207665 / 64) + (-2122095 / 32)*X^(1 : ℕ) + (16407993 / 512)*X^(2 : ℕ) + (1024127 / 1024)*X^(3 : ℕ) + (7963857 / 16384)*X^(4 : ℕ) + (-30027 / 16384)*X^(5 : ℕ) + (5133 / 65536)*X^(6 : ℕ)
  have he3 : 2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ (2 : ℕ) = M^(2 : ℕ)*p3 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4, hh6, hh8, hh10]
    dsimp [p3]
    ring
  let p4 (X : ℂ) : ℂ := (85066245 / 64) + (-1591823865 / 256)*X^(1 : ℕ) + (2049802467 / 512)*X^(2 : ℕ) + (327670217 / 2048)*X^(3 : ℕ) + (1966854177 / 16384)*X^(4 : ℕ) + (-62366877 / 65536)*X^(5 : ℕ) + (3218985 / 65536)*X^(6 : ℕ) + (-725859 / 262144)*X^(7 : ℕ)
  have he4 : -2 * f 0 * f 10 - 90 * f 2 * f 8 - 420 * f 4 * f 6 = M^(2 : ℕ)*p4 (R^(2 : ℕ)) := by
    dsimp [f]
    simp only [hh0, hh2, hh4, hh6, hh8, hh10, hh12]
    dsimp [p4]
    ring
  change signedEvenHankelThreeDetC (-2 * f 0 * f 2) (2 * f 0 * f 4 + 6 * f 2 ^ (2 : ℕ)) (-2 * f 0 * f 6 - 30 * f 2 * f 4) (2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ (2 : ℕ)) (-2 * f 0 * f 10 - 90 * f 2 * f 8 - 420 * f 4 * f 6) = _
  rw [he0,he1,he2,he3,he4]
  have hscale (a b c d e : ℂ) :
      signedEvenHankelThreeDetC (M^(2 : ℕ)*a) (M^(2 : ℕ)*b) (M^(2 : ℕ)*c) (M^(2 : ℕ)*d) (M^(2 : ℕ)*e) =
      M^(6 : ℕ)*signedEvenHankelThreeDetC a b c d e := by
    unfold signedEvenHankelThreeDetC
    ring
  rw [hscale]
  congr 1
  have hp (X : ℂ) : signedEvenHankelThreeDetC (p0 X) (p1 X) (p2 X) (p3 X) (p4 X) =
      modularThetaReflectedTenthSeamPolynomial X := by
    dsimp [p0,p1,p2,p3,p4,signedEvenHankelThreeDetC,modularThetaReflectedTenthSeamPolynomial]
    ring
  exact hp (R^(2 : ℕ))


/-- The analytic modular ODE supplies every jet premise in the elimination. -/
theorem modularThetaReflectedTenthSeamClosure_of_ode
    (M R : ℂ) (h z r p : ℝ → ℂ)
    (hhc : ContDiff ℝ ∞ h) (hzc : ContDiff ℝ ∞ z)
    (hrc : ContDiff ℝ ∞ r) (hpc : ContDiff ℝ ∞ p)
    (hh0 : h 0 = M) (hz0 : z 0 = 0)
    (hr0 : r 0 = R) (hp0 : p 0 = 0)
    (hh' : ∀ x, deriv h x =
      -(1 / 6 : ℂ) * (h x * (p x + r x * z x)))
    (hz' : ∀ x, deriv z x =
      -(r x * (1 - z x * z x)))
    (hr' : ∀ x, deriv r x =
      -(2 / 3 : ℂ) * (r x * (p x + r x * z x)))
    (hp' : ∀ x, deriv p x =
      3 - (1 / 3 : ℂ) * (p x * p x) +
        (1 / 12 : ℂ) * ((r x * r x) * (3 + z x * z x))) :
    let f : ℕ → ℂ := fun n =>
      (iteratedDeriv (n + 2) h 0 -
        (1 / 4 : ℂ) * iteratedDeriv n h 0) / 2
    signedEvenHankelThreeDetC
      (-2 * f 0 * f 2)
      (2 * f 0 * f 4 + 6 * f 2 ^ (2 : ℕ))
      (-2 * f 0 * f 6 - 30 * f 2 * f 4)
      (2 * f 0 * f 8 + 56 * f 2 * f 6 + 70 * f 4 ^ (2 : ℕ))
      (-2 * f 0 * f 10 - 90 * f 2 * f 8 - 420 * f 4 * f 6) =
      M ^ (6 : ℕ) * modularThetaReflectedTenthSeamPolynomial (R ^ (2 : ℕ)) := by
  let jh : ℕ → ℂ := fun n => iteratedDeriv n h 0
  let jz : ℕ → ℂ := fun n => iteratedDeriv n z 0
  let jr : ℕ → ℂ := fun n => iteratedDeriv n r 0
  let jp : ℕ → ℂ := fun n => iteratedDeriv n p 0
  have hunit (n : ℕ) :
      iteratedDeriv n (fun _ : ℝ => (1 : ℂ)) 0 =
        scalarJetUnit n := by
    cases n <;> simp [scalarJetUnit, iteratedDeriv_const]
  have hconst3 (n : ℕ) :
      iteratedDeriv n (fun _ : ℝ => (3 : ℂ)) 0 =
        3 * scalarJetUnit n := by
    cases n <;> simp [scalarJetUnit, iteratedDeriv_const]
  have hmul (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (n : ℕ) :
      iteratedDeriv n (f * g) 0 =
        scalarJetConvolution
          (fun k => iteratedDeriv k f 0)
          (fun k => iteratedDeriv k g 0) n := by
    exact iteratedDeriv_mul
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have hadd (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (n : ℕ) :
      iteratedDeriv n (f + g) 0 =
        iteratedDeriv n f 0 + iteratedDeriv n g 0 := by
    exact iteratedDeriv_add
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have hsub (f g : ℝ → ℂ) (hf : ContDiff ℝ ∞ f)
      (hg : ContDiff ℝ ∞ g) (n : ℕ) :
      iteratedDeriv n (f - g) 0 =
        iteratedDeriv n f 0 - iteratedDeriv n g 0 := by
    exact iteratedDeriv_sub
      (hf.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      (hg.contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
  have jh0 : jh 0 = M := by simpa [jh] using hh0
  have jz0 : jz 0 = 0 := by simpa [jz] using hz0
  have jr0 : jr 0 = R := by simpa [jr] using hr0
  have jp0 : jp 0 = 0 := by simpa [jp] using hp0
  have jhrec (n : ℕ) :
      jh (n + 1) =
        -(1 / 6 : ℂ) *
          scalarJetConvolution jh
            (fun k => jp k + scalarJetConvolution jr jz k) n := by
    simp only [jh, jp, jr, jz]
    rw [iteratedDeriv_succ']
    have heq : deriv h = fun x =>
        -(1 / 6 : ℂ) * (h x * (p x + r x * z x)) :=
      funext hh'
    rw [heq]
    rw [iteratedDeriv_const_mul (-(1 / 6 : ℂ))
      ((hhc.mul (hpc.add (hrc.mul hzc))).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change -(1 / 6 : ℂ) *
        iteratedDeriv n (h * (p + r * z)) 0 = _
    rw [hmul h (p + r * z) hhc
      (hpc.add (hrc.mul hzc)) n]
    unfold scalarJetConvolution
    apply congrArg (fun q : ℂ => -(1 / 6 : ℂ) * q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only
    rw [hadd p (r * z) hpc (hrc.mul hzc)]
    rw [hmul r z hrc hzc]
    rfl
  have jzrec (n : ℕ) :
      jz (n + 1) =
        -scalarJetConvolution jr
          (fun k => scalarJetUnit k -
            scalarJetConvolution jz jz k) n := by
    simp only [jz, jr]
    rw [iteratedDeriv_succ']
    have heq : deriv z = fun x =>
        (-1 : ℂ) * (r x * (1 - z x * z x)) := by
      funext x
      rw [hz']
      ring
    rw [heq]
    rw [iteratedDeriv_const_mul (-1 : ℂ)
      ((hrc.mul (contDiff_const.sub (hzc.mul hzc))).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change (-1 : ℂ) *
        iteratedDeriv n (r * ((fun _ : ℝ => (1 : ℂ)) - z * z)) 0 = _
    rw [hmul r ((fun _ : ℝ => (1 : ℂ)) - z * z) hrc
      (contDiff_const.sub (hzc.mul hzc)) n]
    unfold scalarJetConvolution
    rw [neg_one_mul]
    apply congrArg (fun q : ℂ => -q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only
    rw [hsub (fun _ : ℝ => (1 : ℂ)) (z * z)
      contDiff_const (hzc.mul hzc), hunit]
    rw [hmul z z hzc hzc]
    rfl
  have jrrec (n : ℕ) :
      jr (n + 1) =
        -(2 / 3 : ℂ) *
          scalarJetConvolution jr
            (fun k => jp k + scalarJetConvolution jr jz k) n := by
    simp only [jr, jp, jz]
    rw [iteratedDeriv_succ']
    have heq : deriv r = fun x =>
        -(2 / 3 : ℂ) * (r x * (p x + r x * z x)) :=
      funext hr'
    rw [heq]
    rw [iteratedDeriv_const_mul (-(2 / 3 : ℂ))
      ((hrc.mul (hpc.add (hrc.mul hzc))).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change -(2 / 3 : ℂ) *
        iteratedDeriv n (r * (p + r * z)) 0 = _
    rw [hmul r (p + r * z) hrc
      (hpc.add (hrc.mul hzc)) n]
    unfold scalarJetConvolution
    apply congrArg (fun q : ℂ => -(2 / 3 : ℂ) * q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    simp only
    rw [hadd p (r * z) hpc (hrc.mul hzc)]
    rw [hmul r z hrc hzc]
    rfl
  have jprec (n : ℕ) :
      jp (n + 1) =
        3 * scalarJetUnit n -
          (1 / 3 : ℂ) * scalarJetConvolution jp jp n +
          (1 / 12 : ℂ) *
            scalarJetConvolution (scalarJetConvolution jr jr)
              (fun k => 3 * scalarJetUnit k +
                scalarJetConvolution jz jz k) n := by
    simp only [jp, jr, jz]
    rw [iteratedDeriv_succ']
    have heq : deriv p = fun x =>
        3 - (1 / 3 : ℂ) * (p x * p x) +
          (1 / 12 : ℂ) * ((r x * r x) * (3 + z x * z x)) :=
      funext hp'
    rw [heq]
    change iteratedDeriv n
        ((fun x : ℝ => (3 : ℂ) - (1 / 3 : ℂ) * (p x * p x)) +
          fun x : ℝ =>
            (1 / 12 : ℂ) * ((r x * r x) * (3 + z x * z x))) 0 = _
    rw [iteratedDeriv_add
      ((contDiff_const.sub
        (contDiff_const.mul (hpc.mul hpc))).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))
      ((contDiff_const.mul ((hrc.mul hrc).mul
        (contDiff_const.add (hzc.mul hzc)))).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change
      iteratedDeriv n
          ((fun _ : ℝ => (3 : ℂ)) -
            fun x => (1 / 3 : ℂ) * (p x * p x)) 0 +
        iteratedDeriv n
          (fun x => (1 / 12 : ℂ) *
            ((r x * r x) * (3 + z x * z x))) 0 = _
    rw [iteratedDeriv_sub contDiffAt_const
      ((contDiff_const.mul (hpc.mul hpc)).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    rw [hconst3]
    rw [iteratedDeriv_const_mul (1 / 3 : ℂ)
      ((hpc.mul hpc).contDiffAt.of_le
        (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change
      3 * scalarJetUnit n -
          (1 / 3 : ℂ) * iteratedDeriv n (p * p) 0 +
        iteratedDeriv n
          (fun x => (1 / 12 : ℂ) *
            ((r x * r x) * (3 + z x * z x))) 0 = _
    rw [hmul p p hpc hpc]
    rw [iteratedDeriv_const_mul (1 / 12 : ℂ)
      (((hrc.mul hrc).mul
        (contDiff_const.add (hzc.mul hzc))).contDiffAt.of_le
          (by exact_mod_cast (le_top : ((n : ℕ) : ℕ∞) ≤ ⊤)))]
    change
      3 * scalarJetUnit n -
          (1 / 3 : ℂ) *
            scalarJetConvolution
              (fun k => iteratedDeriv k p 0)
              (fun k => iteratedDeriv k p 0) n +
        (1 / 12 : ℂ) *
          iteratedDeriv n
            ((r * r) * ((fun _ : ℝ => (3 : ℂ)) + z * z)) 0 = _
    rw [hmul (r * r) ((fun _ : ℝ => (3 : ℂ)) + z * z)
      (hrc.mul hrc) (contDiff_const.add (hzc.mul hzc)) n]
    unfold scalarJetConvolution
    apply congrArg (fun q : ℂ =>
      3 * scalarJetUnit n -
          (1 / 3 : ℂ) *
            scalarJetConvolution
              (fun k => iteratedDeriv k p 0)
              (fun k => iteratedDeriv k p 0) n +
        (1 / 12 : ℂ) * q)
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    · simp only
      rw [hmul r r hrc hrc]
      rfl
    · simp only
      rw [hadd (fun _ : ℝ => (3 : ℂ)) (z * z)
            contDiff_const (hzc.mul hzc),
          hconst3, hmul z z hzc hzc]
      rfl
  exact modularThetaReflectedTenthSeamJetElimination M R jh jz jr jp
    jh0 jz0 jr0 jp0 jhrec jzrec jrrec jprec


/-- The odd seam polynomial is strictly negative throughout the physical scale box. -/
theorem modularThetaReflectedTenthSeamPolynomial_neg
    {X : ℝ} (hlo : (191 / 10 : ℝ) ≤ X) (hhi : X ≤ 20) :
    modularThetaReflectedTenthSeamPolynomial X < 0 := by
  let y := X - (191 / 10 : ℝ)
  have hy : 0 ≤ y := by dsimp [y]; linarith
  have hy1 : y ≤ 1 := by dsimp [y]; linarith
  have hp (n : ℕ) : 0 ≤ 1 - y ^ n := sub_nonneg.mpr (pow_le_one₀ hy hy1)
  have hp10 := hp 10
  have hp11 := hp 11
  have hp12 := hp 12
  have hp13 := hp 13
  have hp14 := hp 14
  have hp15 := hp 15
  have hid : -modularThetaReflectedTenthSeamPolynomial X =
    (3080564923922620491692066740103039457303 / 879609302220800000000000) +
    (288928943152129489135184947353297944079 / 87960930222080000000000) * y ^ (1 : ℕ) +
    (11321713529114845042401117131584954431 / 8796093022208000000000) * y ^ (2 : ℕ) +
    (253119115555290587202283703900801943 / 879609302220800000000) * y ^ (3 : ℕ) +
    (3659802059631348335832242882094531 / 87960930222080000000) * y ^ (4 : ℕ) +
    (36394175284728826123552042590939 / 8796093022208000000) * y ^ (5 : ℕ) +
    (255841041175510266612905628123 / 879609302220800000) * y ^ (6 : ℕ) +
    (1270263926884626239933284947 / 87960930222080000) * y ^ (7 : ℕ) +
    (4263297908633393345054181 / 8796093022208000) * y ^ (8 : ℕ) +
    (8062147230190312679757 / 879609302220800) * y ^ (9 : ℕ) +
    (1437012024369451011 / 87960930222080) * (1 - y ^ (10 : ℕ)) +
    (59484862171607931 / 8796093022208) * (1 - y ^ (11 : ℕ)) +
    (930978403404795 / 4398046511104) * (1 - y ^ (12 : ℕ)) +
    (7596952502175 / 2199023255552) * (1 - y ^ (13 : ℕ)) +
    (33695674875 / 1099511627776) * (1 - y ^ (14 : ℕ)) +
    (64029375 / 549755813888) * (1 - y ^ (15 : ℕ)) := by
    dsimp [y, modularThetaReflectedTenthSeamPolynomial]
    ring
  have hpos : 0 < -modularThetaReflectedTenthSeamPolynomial X := by
    rw [hid]
    positivity
  linarith

end
end HTGeometry
