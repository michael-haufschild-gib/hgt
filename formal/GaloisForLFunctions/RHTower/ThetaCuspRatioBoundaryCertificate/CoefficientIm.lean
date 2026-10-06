import GaloisForLFunctions.RHTower.ThetaCuspRatioBoundaryCertificate.Bernstein

namespace HTGeometry.ThetaRatioInfinity

noncomputable section

def boundaryImCoefficient77_0 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 (((258052183/272097792 : ℝ))/3) ((21-0)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((258052183/272097792 : ℝ))/36) (((21-0)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((258052183/272097792 : ℝ))/216) (((21-0)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((6510854519/9795520512 : ℝ))/3) ((21-0)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((6510854519/9795520512 : ℝ))/36) (((21-0)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((6510854519/9795520512 : ℝ))/216) (((21-0)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((-186364574969/1410554953728 : ℝ))/3) ((21-0)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-186364574969/1410554953728 : ℝ))/36) (((21-0)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-186364574969/1410554953728 : ℝ))/216) (((21-0)+2*2-5)+2) 1 2 A B)))) + ((((boundaryTermCoefficient77 (((-1033797574409/12694994583552 : ℝ))/3) ((21-0)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-1033797574409/12694994583552 : ℝ))/36) (((21-0)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-1033797574409/12694994583552 : ℝ))/216) (((21-0)+2*3-5)+2) 1 3 A B)))) + (((boundaryTermCoefficient77 (((12105944831381/7312316880125952 : ℝ))/3) ((21-0)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((12105944831381/7312316880125952 : ℝ))/36) (((21-0)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((12105944831381/7312316880125952 : ℝ))/216) (((21-0)+2*4-5)+2) 1 4 A B))))))) + (((((boundaryTermCoefficient77 (((130377163775405/65810851921133568 : ℝ))/3) ((21-0)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((130377163775405/65810851921133568 : ℝ))/36) (((21-0)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((130377163775405/65810851921133568 : ℝ))/216) (((21-0)+2*5-5)+2) 1 5 A B)))) + (((boundaryTermCoefficient77 (((284835824941/3084883683803136 : ℝ))/3) ((21-0)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((284835824941/3084883683803136 : ℝ))/36) (((21-0)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((284835824941/3084883683803136 : ℝ))/216) (((21-0)+2*6-5)+2) 1 6 A B))))) + ((((boundaryTermCoefficient77 (((-47428789322903/2665339502805909504 : ℝ))/3) ((21-0)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-47428789322903/2665339502805909504 : ℝ))/36) (((21-0)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-47428789322903/2665339502805909504 : ℝ))/216) (((21-0)+2*7-5)+2) 1 7 A B)))) + ((((boundaryTermCoefficient77 (((-9987025493561/5330679005611819008 : ℝ))/3) ((21-0)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-9987025493561/5330679005611819008 : ℝ))/36) (((21-0)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-9987025493561/5330679005611819008 : ℝ))/216) (((21-0)+2*8-5)+2) 1 8 A B)))) + (((boundaryTermCoefficient77 (((63860187804325/431784999454557339648 : ℝ))/3) ((21-0)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((63860187804325/431784999454557339648 : ℝ))/36) (((21-0)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((63860187804325/431784999454557339648 : ℝ))/216) (((21-0)+2*9-5)+2) 1 9 A B))))))))

theorem boundaryImCoefficient77_0_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_0 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_0 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_0

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((258052183/272097792 : ℝ))/3) ((21-0)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((258052183/272097792 : ℝ))/36) (((21-0)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((258052183/272097792 : ℝ))/216) (((21-0)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((6510854519/9795520512 : ℝ))/3) ((21-0)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((6510854519/9795520512 : ℝ))/36) (((21-0)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((6510854519/9795520512 : ℝ))/216) (((21-0)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-186364574969/1410554953728 : ℝ))/3) ((21-0)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-186364574969/1410554953728 : ℝ))/36) (((21-0)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-186364574969/1410554953728 : ℝ))/216) (((21-0)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1033797574409/12694994583552 : ℝ))/3) ((21-0)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1033797574409/12694994583552 : ℝ))/36) (((21-0)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1033797574409/12694994583552 : ℝ))/216) (((21-0)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((12105944831381/7312316880125952 : ℝ))/3) ((21-0)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((12105944831381/7312316880125952 : ℝ))/36) (((21-0)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((12105944831381/7312316880125952 : ℝ))/216) (((21-0)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((130377163775405/65810851921133568 : ℝ))/3) ((21-0)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((130377163775405/65810851921133568 : ℝ))/36) (((21-0)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((130377163775405/65810851921133568 : ℝ))/216) (((21-0)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((284835824941/3084883683803136 : ℝ))/3) ((21-0)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((284835824941/3084883683803136 : ℝ))/36) (((21-0)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((284835824941/3084883683803136 : ℝ))/216) (((21-0)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-47428789322903/2665339502805909504 : ℝ))/3) ((21-0)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-47428789322903/2665339502805909504 : ℝ))/36) (((21-0)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-47428789322903/2665339502805909504 : ℝ))/216) (((21-0)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-9987025493561/5330679005611819008 : ℝ))/3) ((21-0)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-9987025493561/5330679005611819008 : ℝ))/36) (((21-0)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-9987025493561/5330679005611819008 : ℝ))/216) (((21-0)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((63860187804325/431784999454557339648 : ℝ))/3) ((21-0)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((63860187804325/431784999454557339648 : ℝ))/36) (((21-0)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((63860187804325/431784999454557339648 : ℝ))/216) (((21-0)+2*9-5)+2) 1 9 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_0,boundaryZ77]

  ring


def boundaryImCoefficient77_1 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 (((347952563/15116544 : ℝ))/3) ((21-1)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((347952563/15116544 : ℝ))/36) (((21-1)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((347952563/15116544 : ℝ))/216) (((21-1)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((133551734933/19591041024 : ℝ))/3) ((21-1)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((133551734933/19591041024 : ℝ))/36) (((21-1)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((133551734933/19591041024 : ℝ))/216) (((21-1)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((-2312978499941/470184984576 : ℝ))/3) ((21-1)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-2312978499941/470184984576 : ℝ))/36) (((21-1)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-2312978499941/470184984576 : ℝ))/216) (((21-1)+2*2-5)+2) 1 2 A B)))) + ((((boundaryTermCoefficient77 (((-4421341459327/5642219814912 : ℝ))/3) ((21-1)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-4421341459327/5642219814912 : ℝ))/36) (((21-1)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-4421341459327/5642219814912 : ℝ))/216) (((21-1)+2*3-5)+2) 1 3 A B)))) + (((boundaryTermCoefficient77 (((1248266550682421/7312316880125952 : ℝ))/3) ((21-1)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((1248266550682421/7312316880125952 : ℝ))/36) (((21-1)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((1248266550682421/7312316880125952 : ℝ))/216) (((21-1)+2*4-5)+2) 1 4 A B))))))) + (((((boundaryTermCoefficient77 (((1404956250307805/87747802561511424 : ℝ))/3) ((21-1)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((1404956250307805/87747802561511424 : ℝ))/36) (((21-1)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((1404956250307805/87747802561511424 : ℝ))/216) (((21-1)+2*5-5)+2) 1 5 A B)))) + ((((boundaryTermCoefficient77 (((-3334177576970155/1184595334580404224 : ℝ))/3) ((21-1)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((-3334177576970155/1184595334580404224 : ℝ))/36) (((21-1)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((-3334177576970155/1184595334580404224 : ℝ))/216) (((21-1)+2*6-5)+2) 1 6 A B)))) + (((boundaryTermCoefficient77 (((-293867481139519/2369190669160808448 : ℝ))/3) ((21-1)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-293867481139519/2369190669160808448 : ℝ))/36) (((21-1)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-293867481139519/2369190669160808448 : ℝ))/216) (((21-1)+2*7-5)+2) 1 7 A B)))))) + ((((boundaryTermCoefficient77 (((12980928713958509/191904444202025484288 : ℝ))/3) ((21-1)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((12980928713958509/191904444202025484288 : ℝ))/36) (((21-1)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((12980928713958509/191904444202025484288 : ℝ))/216) (((21-1)+2*8-5)+2) 1 8 A B)))) + ((((boundaryTermCoefficient77 (((-1380000928479463/215892499727278669824 : ℝ))/3) ((21-1)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-1380000928479463/215892499727278669824 : ℝ))/36) (((21-1)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-1380000928479463/215892499727278669824 : ℝ))/216) (((21-1)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((2763132821290541/15544259980364064227328 : ℝ))/3) ((21-1)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((2763132821290541/15544259980364064227328 : ℝ))/36) (((21-1)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((2763132821290541/15544259980364064227328 : ℝ))/216) (((21-1)+2*10-5)+2) 1 10 A B))))))))

theorem boundaryImCoefficient77_1_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_1 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_1 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_1

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((347952563/15116544 : ℝ))/3) ((21-1)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((347952563/15116544 : ℝ))/36) (((21-1)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((347952563/15116544 : ℝ))/216) (((21-1)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((133551734933/19591041024 : ℝ))/3) ((21-1)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((133551734933/19591041024 : ℝ))/36) (((21-1)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((133551734933/19591041024 : ℝ))/216) (((21-1)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2312978499941/470184984576 : ℝ))/3) ((21-1)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2312978499941/470184984576 : ℝ))/36) (((21-1)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2312978499941/470184984576 : ℝ))/216) (((21-1)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-4421341459327/5642219814912 : ℝ))/3) ((21-1)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-4421341459327/5642219814912 : ℝ))/36) (((21-1)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-4421341459327/5642219814912 : ℝ))/216) (((21-1)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1248266550682421/7312316880125952 : ℝ))/3) ((21-1)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1248266550682421/7312316880125952 : ℝ))/36) (((21-1)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1248266550682421/7312316880125952 : ℝ))/216) (((21-1)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1404956250307805/87747802561511424 : ℝ))/3) ((21-1)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1404956250307805/87747802561511424 : ℝ))/36) (((21-1)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1404956250307805/87747802561511424 : ℝ))/216) (((21-1)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-3334177576970155/1184595334580404224 : ℝ))/3) ((21-1)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-3334177576970155/1184595334580404224 : ℝ))/36) (((21-1)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-3334177576970155/1184595334580404224 : ℝ))/216) (((21-1)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-293867481139519/2369190669160808448 : ℝ))/3) ((21-1)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-293867481139519/2369190669160808448 : ℝ))/36) (((21-1)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-293867481139519/2369190669160808448 : ℝ))/216) (((21-1)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((12980928713958509/191904444202025484288 : ℝ))/3) ((21-1)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((12980928713958509/191904444202025484288 : ℝ))/36) (((21-1)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((12980928713958509/191904444202025484288 : ℝ))/216) (((21-1)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1380000928479463/215892499727278669824 : ℝ))/3) ((21-1)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1380000928479463/215892499727278669824 : ℝ))/36) (((21-1)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1380000928479463/215892499727278669824 : ℝ))/216) (((21-1)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((2763132821290541/15544259980364064227328 : ℝ))/3) ((21-1)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((2763132821290541/15544259980364064227328 : ℝ))/36) (((21-1)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((2763132821290541/15544259980364064227328 : ℝ))/216) (((21-1)+2*10-5)+2) 1 10 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_1,boundaryZ77]

  ring


def boundaryImCoefficient77_2 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 (((17921951587/90699264 : ℝ))/3) ((21-2)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((17921951587/90699264 : ℝ))/36) (((21-2)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((17921951587/90699264 : ℝ))/216) (((21-2)+2*0-5)+2) 1 0 A B)))) + ((((boundaryTermCoefficient77 (((-596954040563/19591041024 : ℝ))/3) ((21-2)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((-596954040563/19591041024 : ℝ))/36) (((21-2)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((-596954040563/19591041024 : ℝ))/216) (((21-2)+2*1-5)+2) 1 1 A B)))) + (((boundaryTermCoefficient77 (((-9899750372263/235092492288 : ℝ))/3) ((21-2)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-9899750372263/235092492288 : ℝ))/36) (((21-2)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-9899750372263/235092492288 : ℝ))/216) (((21-2)+2*2-5)+2) 1 2 A B)))))) + ((((boundaryTermCoefficient77 (((429128690993677/101559956668416 : ℝ))/3) ((21-2)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((429128690993677/101559956668416 : ℝ))/36) (((21-2)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((429128690993677/101559956668416 : ℝ))/216) (((21-2)+2*3-5)+2) 1 3 A B)))) + ((((boundaryTermCoefficient77 (((264069531291865/304679870005248 : ℝ))/3) ((21-2)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((264069531291865/304679870005248 : ℝ))/36) (((21-2)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((264069531291865/304679870005248 : ℝ))/216) (((21-2)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-7183393786654495/29249267520503808 : ℝ))/3) ((21-2)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-7183393786654495/29249267520503808 : ℝ))/36) (((21-2)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-7183393786654495/29249267520503808 : ℝ))/216) (((21-2)+2*5-5)+2) 1 5 A B))))))) + (((((boundaryTermCoefficient77 (((26953734167286863/3158920892214411264 : ℝ))/3) ((21-2)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((26953734167286863/3158920892214411264 : ℝ))/36) (((21-2)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((26953734167286863/3158920892214411264 : ℝ))/216) (((21-2)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((275968457834471069/42645432044894552064 : ℝ))/3) ((21-2)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((275968457834471069/42645432044894552064 : ℝ))/36) (((21-2)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((275968457834471069/42645432044894552064 : ℝ))/216) (((21-2)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((-1709798571567940855/1535235553616203874304 : ℝ))/3) ((21-2)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-1709798571567940855/1535235553616203874304 : ℝ))/36) (((21-2)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-1709798571567940855/1535235553616203874304 : ℝ))/216) (((21-2)+2*8-5)+2) 1 8 A B)))))) + ((((boundaryTermCoefficient77 (((600569426788768079/6908559991272917434368 : ℝ))/3) ((21-2)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((600569426788768079/6908559991272917434368 : ℝ))/36) (((21-2)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((600569426788768079/6908559991272917434368 : ℝ))/216) (((21-2)+2*9-5)+2) 1 9 A B)))) + ((((boundaryTermCoefficient77 (((-46690054739436401/13817119982545834868736 : ℝ))/3) ((21-2)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((-46690054739436401/13817119982545834868736 : ℝ))/36) (((21-2)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((-46690054739436401/13817119982545834868736 : ℝ))/216) (((21-2)+2*10-5)+2) 1 10 A B)))) + (((boundaryTermCoefficient77 (((12177572871726983/279796679646553156091904 : ℝ))/3) ((21-2)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((12177572871726983/279796679646553156091904 : ℝ))/36) (((21-2)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((12177572871726983/279796679646553156091904 : ℝ))/216) (((21-2)+2*11-5)+2) 1 11 A B))))))))

theorem boundaryImCoefficient77_2_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_2 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_2 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_2

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((17921951587/90699264 : ℝ))/3) ((21-2)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((17921951587/90699264 : ℝ))/36) (((21-2)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((17921951587/90699264 : ℝ))/216) (((21-2)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-596954040563/19591041024 : ℝ))/3) ((21-2)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-596954040563/19591041024 : ℝ))/36) (((21-2)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-596954040563/19591041024 : ℝ))/216) (((21-2)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-9899750372263/235092492288 : ℝ))/3) ((21-2)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-9899750372263/235092492288 : ℝ))/36) (((21-2)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-9899750372263/235092492288 : ℝ))/216) (((21-2)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((429128690993677/101559956668416 : ℝ))/3) ((21-2)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((429128690993677/101559956668416 : ℝ))/36) (((21-2)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((429128690993677/101559956668416 : ℝ))/216) (((21-2)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((264069531291865/304679870005248 : ℝ))/3) ((21-2)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((264069531291865/304679870005248 : ℝ))/36) (((21-2)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((264069531291865/304679870005248 : ℝ))/216) (((21-2)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-7183393786654495/29249267520503808 : ℝ))/3) ((21-2)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-7183393786654495/29249267520503808 : ℝ))/36) (((21-2)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-7183393786654495/29249267520503808 : ℝ))/216) (((21-2)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((26953734167286863/3158920892214411264 : ℝ))/3) ((21-2)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((26953734167286863/3158920892214411264 : ℝ))/36) (((21-2)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((26953734167286863/3158920892214411264 : ℝ))/216) (((21-2)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((275968457834471069/42645432044894552064 : ℝ))/3) ((21-2)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((275968457834471069/42645432044894552064 : ℝ))/36) (((21-2)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((275968457834471069/42645432044894552064 : ℝ))/216) (((21-2)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1709798571567940855/1535235553616203874304 : ℝ))/3) ((21-2)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1709798571567940855/1535235553616203874304 : ℝ))/36) (((21-2)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1709798571567940855/1535235553616203874304 : ℝ))/216) (((21-2)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((600569426788768079/6908559991272917434368 : ℝ))/3) ((21-2)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((600569426788768079/6908559991272917434368 : ℝ))/36) (((21-2)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((600569426788768079/6908559991272917434368 : ℝ))/216) (((21-2)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-46690054739436401/13817119982545834868736 : ℝ))/3) ((21-2)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-46690054739436401/13817119982545834868736 : ℝ))/36) (((21-2)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-46690054739436401/13817119982545834868736 : ℝ))/216) (((21-2)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((12177572871726983/279796679646553156091904 : ℝ))/3) ((21-2)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((12177572871726983/279796679646553156091904 : ℝ))/36) (((21-2)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((12177572871726983/279796679646553156091904 : ℝ))/216) (((21-2)+2*11-5)+2) 1 11 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_2,boundaryZ77]

  ring


def boundaryImCoefficient77_3 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 (((4433739133/8503056 : ℝ))/3) ((21-3)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((4433739133/8503056 : ℝ))/36) (((21-3)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((4433739133/8503056 : ℝ))/216) (((21-3)+2*0-5)+2) 1 0 A B)))) + ((((boundaryTermCoefficient77 (((-5748284649001/9795520512 : ℝ))/3) ((21-3)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((-5748284649001/9795520512 : ℝ))/36) (((21-3)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((-5748284649001/9795520512 : ℝ))/216) (((21-3)+2*1-5)+2) 1 1 A B)))) + (((boundaryTermCoefficient77 (((-25425160016345/1410554953728 : ℝ))/3) ((21-3)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-25425160016345/1410554953728 : ℝ))/36) (((21-3)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-25425160016345/1410554953728 : ℝ))/216) (((21-3)+2*2-5)+2) 1 2 A B)))))) + ((((boundaryTermCoefficient77 (((3798237873321137/101559956668416 : ℝ))/3) ((21-3)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((3798237873321137/101559956668416 : ℝ))/36) (((21-3)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((3798237873321137/101559956668416 : ℝ))/216) (((21-3)+2*3-5)+2) 1 3 A B)))) + ((((boundaryTermCoefficient77 (((-36297245462526875/3656158440062976 : ℝ))/3) ((21-3)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-36297245462526875/3656158440062976 : ℝ))/36) (((21-3)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-36297245462526875/3656158440062976 : ℝ))/216) (((21-3)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((5189128058942131/14624633760251904 : ℝ))/3) ((21-3)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((5189128058942131/14624633760251904 : ℝ))/36) (((21-3)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((5189128058942131/14624633760251904 : ℝ))/216) (((21-3)+2*5-5)+2) 1 5 A B))))))) + (((((boundaryTermCoefficient77 (((5839049016890081813/18953525353286467584 : ℝ))/3) ((21-3)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((5839049016890081813/18953525353286467584 : ℝ))/36) (((21-3)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((5839049016890081813/18953525353286467584 : ℝ))/216) (((21-3)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((-85389012600265476499/1364653825436625666048 : ℝ))/3) ((21-3)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-85389012600265476499/1364653825436625666048 : ℝ))/36) (((21-3)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-85389012600265476499/1364653825436625666048 : ℝ))/216) (((21-3)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((9824350396117451999/1535235553616203874304 : ℝ))/3) ((21-3)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((9824350396117451999/1535235553616203874304 : ℝ))/36) (((21-3)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((9824350396117451999/1535235553616203874304 : ℝ))/216) (((21-3)+2*8-5)+2) 1 8 A B)))))) + (((((boundaryTermCoefficient77 (((-5056817636319640633/12281884428929630994432 : ℝ))/3) ((21-3)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-5056817636319640633/12281884428929630994432 : ℝ))/36) (((21-3)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-5056817636319640633/12281884428929630994432 : ℝ))/216) (((21-3)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((6199201151966658827/331610879581100036849664 : ℝ))/3) ((21-3)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((6199201151966658827/331610879581100036849664 : ℝ))/36) (((21-3)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((6199201151966658827/331610879581100036849664 : ℝ))/216) (((21-3)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((-131755225973988043/279796679646553156091904 : ℝ))/3) ((21-3)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-131755225973988043/279796679646553156091904 : ℝ))/36) (((21-3)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-131755225973988043/279796679646553156091904 : ℝ))/216) (((21-3)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((259263771223410611/80581443738207308954468352 : ℝ))/3) ((21-3)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((259263771223410611/80581443738207308954468352 : ℝ))/36) (((21-3)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((259263771223410611/80581443738207308954468352 : ℝ))/216) (((21-3)+2*12-5)+2) 1 12 A B))))))))

theorem boundaryImCoefficient77_3_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_3 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_3 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_3

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((4433739133/8503056 : ℝ))/3) ((21-3)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((4433739133/8503056 : ℝ))/36) (((21-3)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((4433739133/8503056 : ℝ))/216) (((21-3)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-5748284649001/9795520512 : ℝ))/3) ((21-3)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-5748284649001/9795520512 : ℝ))/36) (((21-3)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-5748284649001/9795520512 : ℝ))/216) (((21-3)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-25425160016345/1410554953728 : ℝ))/3) ((21-3)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-25425160016345/1410554953728 : ℝ))/36) (((21-3)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-25425160016345/1410554953728 : ℝ))/216) (((21-3)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((3798237873321137/101559956668416 : ℝ))/3) ((21-3)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((3798237873321137/101559956668416 : ℝ))/36) (((21-3)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((3798237873321137/101559956668416 : ℝ))/216) (((21-3)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-36297245462526875/3656158440062976 : ℝ))/3) ((21-3)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-36297245462526875/3656158440062976 : ℝ))/36) (((21-3)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-36297245462526875/3656158440062976 : ℝ))/216) (((21-3)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((5189128058942131/14624633760251904 : ℝ))/3) ((21-3)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((5189128058942131/14624633760251904 : ℝ))/36) (((21-3)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((5189128058942131/14624633760251904 : ℝ))/216) (((21-3)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((5839049016890081813/18953525353286467584 : ℝ))/3) ((21-3)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((5839049016890081813/18953525353286467584 : ℝ))/36) (((21-3)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((5839049016890081813/18953525353286467584 : ℝ))/216) (((21-3)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-85389012600265476499/1364653825436625666048 : ℝ))/3) ((21-3)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-85389012600265476499/1364653825436625666048 : ℝ))/36) (((21-3)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-85389012600265476499/1364653825436625666048 : ℝ))/216) (((21-3)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((9824350396117451999/1535235553616203874304 : ℝ))/3) ((21-3)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((9824350396117451999/1535235553616203874304 : ℝ))/36) (((21-3)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((9824350396117451999/1535235553616203874304 : ℝ))/216) (((21-3)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-5056817636319640633/12281884428929630994432 : ℝ))/3) ((21-3)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-5056817636319640633/12281884428929630994432 : ℝ))/36) (((21-3)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-5056817636319640633/12281884428929630994432 : ℝ))/216) (((21-3)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((6199201151966658827/331610879581100036849664 : ℝ))/3) ((21-3)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((6199201151966658827/331610879581100036849664 : ℝ))/36) (((21-3)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((6199201151966658827/331610879581100036849664 : ℝ))/216) (((21-3)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-131755225973988043/279796679646553156091904 : ℝ))/3) ((21-3)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-131755225973988043/279796679646553156091904 : ℝ))/36) (((21-3)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-131755225973988043/279796679646553156091904 : ℝ))/216) (((21-3)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((259263771223410611/80581443738207308954468352 : ℝ))/3) ((21-3)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((259263771223410611/80581443738207308954468352 : ℝ))/36) (((21-3)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((259263771223410611/80581443738207308954468352 : ℝ))/216) (((21-3)+2*12-5)+2) 1 12 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_3,boundaryZ77]

  ring


def boundaryImCoefficient77_4 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 (((-526010560219/272097792 : ℝ))/3) ((21-4)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((-526010560219/272097792 : ℝ))/36) (((21-4)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((-526010560219/272097792 : ℝ))/216) (((21-4)+2*0-5)+2) 1 0 A B)))) + ((((boundaryTermCoefficient77 (((-30790866766487/19591041024 : ℝ))/3) ((21-4)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((-30790866766487/19591041024 : ℝ))/36) (((21-4)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((-30790866766487/19591041024 : ℝ))/216) (((21-4)+2*1-5)+2) 1 1 A B)))) + (((boundaryTermCoefficient77 (((108460793539765/156728328192 : ℝ))/3) ((21-4)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((108460793539765/156728328192 : ℝ))/36) (((21-4)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((108460793539765/156728328192 : ℝ))/216) (((21-4)+2*2-5)+2) 1 2 A B)))))) + (((((boundaryTermCoefficient77 (((-1052275049253833/6347497291776 : ℝ))/3) ((21-4)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-1052275049253833/6347497291776 : ℝ))/36) (((21-4)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-1052275049253833/6347497291776 : ℝ))/216) (((21-4)+2*3-5)+2) 1 3 A B)))) + (((boundaryTermCoefficient77 (((-24190683190474379/7312316880125952 : ℝ))/3) ((21-4)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-24190683190474379/7312316880125952 : ℝ))/36) (((21-4)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-24190683190474379/7312316880125952 : ℝ))/216) (((21-4)+2*4-5)+2) 1 4 A B))))) + ((((boundaryTermCoefficient77 (((768886023267285253/65810851921133568 : ℝ))/3) ((21-4)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((768886023267285253/65810851921133568 : ℝ))/36) (((21-4)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((768886023267285253/65810851921133568 : ℝ))/216) (((21-4)+2*5-5)+2) 1 5 A B)))) + (((boundaryTermCoefficient77 (((-87324025383315097261/37907050706572935168 : ℝ))/3) ((21-4)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((-87324025383315097261/37907050706572935168 : ℝ))/36) (((21-4)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((-87324025383315097261/37907050706572935168 : ℝ))/216) (((21-4)+2*6-5)+2) 1 6 A B))))))) + (((((boundaryTermCoefficient77 (((245316404231561318377/1364653825436625666048 : ℝ))/3) ((21-4)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((245316404231561318377/1364653825436625666048 : ℝ))/36) (((21-4)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((245316404231561318377/1364653825436625666048 : ℝ))/216) (((21-4)+2*7-5)+2) 1 7 A B)))) + ((((boundaryTermCoefficient77 (((-326519775830088756265/196510150862874095910912 : ℝ))/3) ((21-4)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-326519775830088756265/196510150862874095910912 : ℝ))/36) (((21-4)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-326519775830088756265/196510150862874095910912 : ℝ))/216) (((21-4)+2*8-5)+2) 1 8 A B)))) + (((boundaryTermCoefficient77 (((-917970537207242003641/1768591357765866863198208 : ℝ))/3) ((21-4)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-917970537207242003641/1768591357765866863198208 : ℝ))/36) (((21-4)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-917970537207242003641/1768591357765866863198208 : ℝ))/216) (((21-4)+2*9-5)+2) 1 9 A B)))))) + (((((boundaryTermCoefficient77 (((15082768023679164271/884295678882933431599104 : ℝ))/3) ((21-4)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((15082768023679164271/884295678882933431599104 : ℝ))/36) (((21-4)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((15082768023679164271/884295678882933431599104 : ℝ))/216) (((21-4)+2*10-5)+2) 1 10 A B)))) + (((boundaryTermCoefficient77 (((43897479471302461307/71627949989517607959527424 : ℝ))/3) ((21-4)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((43897479471302461307/71627949989517607959527424 : ℝ))/36) (((21-4)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((43897479471302461307/71627949989517607959527424 : ℝ))/216) (((21-4)+2*11-5)+2) 1 11 A B))))) + ((((boundaryTermCoefficient77 (((-25566620683021306693/1289303099811316943271493632 : ℝ))/3) ((21-4)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-25566620683021306693/1289303099811316943271493632 : ℝ))/36) (((21-4)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-25566620683021306693/1289303099811316943271493632 : ℝ))/216) (((21-4)+2*12-5)+2) 1 12 A B)))) + (((boundaryTermCoefficient77 (((308296208412382897/3867909299433950829814480896 : ℝ))/3) ((21-4)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((308296208412382897/3867909299433950829814480896 : ℝ))/36) (((21-4)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((308296208412382897/3867909299433950829814480896 : ℝ))/216) (((21-4)+2*13-5)+2) 1 13 A B))))))))

theorem boundaryImCoefficient77_4_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_4 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_4 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_4

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((-526010560219/272097792 : ℝ))/3) ((21-4)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-526010560219/272097792 : ℝ))/36) (((21-4)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-526010560219/272097792 : ℝ))/216) (((21-4)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-30790866766487/19591041024 : ℝ))/3) ((21-4)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-30790866766487/19591041024 : ℝ))/36) (((21-4)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-30790866766487/19591041024 : ℝ))/216) (((21-4)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((108460793539765/156728328192 : ℝ))/3) ((21-4)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((108460793539765/156728328192 : ℝ))/36) (((21-4)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((108460793539765/156728328192 : ℝ))/216) (((21-4)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1052275049253833/6347497291776 : ℝ))/3) ((21-4)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1052275049253833/6347497291776 : ℝ))/36) (((21-4)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1052275049253833/6347497291776 : ℝ))/216) (((21-4)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-24190683190474379/7312316880125952 : ℝ))/3) ((21-4)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-24190683190474379/7312316880125952 : ℝ))/36) (((21-4)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-24190683190474379/7312316880125952 : ℝ))/216) (((21-4)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((768886023267285253/65810851921133568 : ℝ))/3) ((21-4)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((768886023267285253/65810851921133568 : ℝ))/36) (((21-4)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((768886023267285253/65810851921133568 : ℝ))/216) (((21-4)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-87324025383315097261/37907050706572935168 : ℝ))/3) ((21-4)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-87324025383315097261/37907050706572935168 : ℝ))/36) (((21-4)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-87324025383315097261/37907050706572935168 : ℝ))/216) (((21-4)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((245316404231561318377/1364653825436625666048 : ℝ))/3) ((21-4)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((245316404231561318377/1364653825436625666048 : ℝ))/36) (((21-4)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((245316404231561318377/1364653825436625666048 : ℝ))/216) (((21-4)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-326519775830088756265/196510150862874095910912 : ℝ))/3) ((21-4)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-326519775830088756265/196510150862874095910912 : ℝ))/36) (((21-4)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-326519775830088756265/196510150862874095910912 : ℝ))/216) (((21-4)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-917970537207242003641/1768591357765866863198208 : ℝ))/3) ((21-4)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-917970537207242003641/1768591357765866863198208 : ℝ))/36) (((21-4)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-917970537207242003641/1768591357765866863198208 : ℝ))/216) (((21-4)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((15082768023679164271/884295678882933431599104 : ℝ))/3) ((21-4)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((15082768023679164271/884295678882933431599104 : ℝ))/36) (((21-4)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((15082768023679164271/884295678882933431599104 : ℝ))/216) (((21-4)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((43897479471302461307/71627949989517607959527424 : ℝ))/3) ((21-4)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((43897479471302461307/71627949989517607959527424 : ℝ))/36) (((21-4)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((43897479471302461307/71627949989517607959527424 : ℝ))/216) (((21-4)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-25566620683021306693/1289303099811316943271493632 : ℝ))/3) ((21-4)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-25566620683021306693/1289303099811316943271493632 : ℝ))/36) (((21-4)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-25566620683021306693/1289303099811316943271493632 : ℝ))/216) (((21-4)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((308296208412382897/3867909299433950829814480896 : ℝ))/3) ((21-4)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((308296208412382897/3867909299433950829814480896 : ℝ))/36) (((21-4)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((308296208412382897/3867909299433950829814480896 : ℝ))/216) (((21-4)+2*13-5)+2) 1 13 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_4,boundaryZ77]

  ring


def boundaryImCoefficient77_5 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 (((-595134447329/45349632 : ℝ))/3) ((21-5)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((-595134447329/45349632 : ℝ))/36) (((21-5)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((-595134447329/45349632 : ℝ))/216) (((21-5)+2*0-5)+2) 1 0 A B)))) + ((((boundaryTermCoefficient77 (((68246754478747/19591041024 : ℝ))/3) ((21-5)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((68246754478747/19591041024 : ℝ))/36) (((21-5)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((68246754478747/19591041024 : ℝ))/216) (((21-5)+2*1-5)+2) 1 1 A B)))) + (((boundaryTermCoefficient77 (((-139280847775457/235092492288 : ℝ))/3) ((21-5)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-139280847775457/235092492288 : ℝ))/36) (((21-5)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-139280847775457/235092492288 : ℝ))/216) (((21-5)+2*2-5)+2) 1 2 A B)))))) + (((((boundaryTermCoefficient77 (((-653806045063829/1586874322944 : ℝ))/3) ((21-5)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-653806045063829/1586874322944 : ℝ))/36) (((21-5)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-653806045063829/1586874322944 : ℝ))/216) (((21-5)+2*3-5)+2) 1 3 A B)))) + (((boundaryTermCoefficient77 (((576135055035147667/1828079220031488 : ℝ))/3) ((21-5)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((576135055035147667/1828079220031488 : ℝ))/36) (((21-5)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((576135055035147667/1828079220031488 : ℝ))/216) (((21-5)+2*4-5)+2) 1 4 A B))))) + ((((boundaryTermCoefficient77 (((-30144349061698426627/526486815369068544 : ℝ))/3) ((21-5)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-30144349061698426627/526486815369068544 : ℝ))/36) (((21-5)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-30144349061698426627/526486815369068544 : ℝ))/216) (((21-5)+2*5-5)+2) 1 5 A B)))) + (((boundaryTermCoefficient77 (((8535111205340920181/4211894522952548352 : ℝ))/3) ((21-5)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((8535111205340920181/4211894522952548352 : ℝ))/36) (((21-5)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((8535111205340920181/4211894522952548352 : ℝ))/216) (((21-5)+2*6-5)+2) 1 6 A B))))))) + ((((((boundaryTermCoefficient77 (((87540653190844684615/113721152119718805504 : ℝ))/3) ((21-5)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((87540653190844684615/113721152119718805504 : ℝ))/36) (((21-5)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((87540653190844684615/113721152119718805504 : ℝ))/216) (((21-5)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((-27755368091845695374635/196510150862874095910912 : ℝ))/3) ((21-5)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-27755368091845695374635/196510150862874095910912 : ℝ))/36) (((21-5)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-27755368091845695374635/196510150862874095910912 : ℝ))/216) (((21-5)+2*8-5)+2) 1 8 A B))))) + ((((boundaryTermCoefficient77 (((6713613650610981410789/589530452588622287732736 : ℝ))/3) ((21-5)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((6713613650610981410789/589530452588622287732736 : ℝ))/36) (((21-5)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((6713613650610981410789/589530452588622287732736 : ℝ))/216) (((21-5)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((-1959259070331909946855/3979330554973200442195968 : ℝ))/3) ((21-5)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((-1959259070331909946855/3979330554973200442195968 : ℝ))/36) (((21-5)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((-1959259070331909946855/3979330554973200442195968 : ℝ))/216) (((21-5)+2*10-5)+2) 1 10 A B)))))) + (((((boundaryTermCoefficient77 (((701417487728543150753/71627949989517607959527424 : ℝ))/3) ((21-5)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((701417487728543150753/71627949989517607959527424 : ℝ))/36) (((21-5)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((701417487728543150753/71627949989517607959527424 : ℝ))/216) (((21-5)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((-53871599646351098255/1289303099811316943271493632 : ℝ))/3) ((21-5)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-53871599646351098255/1289303099811316943271493632 : ℝ))/36) (((21-5)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-53871599646351098255/1289303099811316943271493632 : ℝ))/216) (((21-5)+2*12-5)+2) 1 12 A B))))) + ((((boundaryTermCoefficient77 (((-2666267823376143329/11603727898301852489443442688 : ℝ))/3) ((21-5)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((-2666267823376143329/11603727898301852489443442688 : ℝ))/36) (((21-5)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((-2666267823376143329/11603727898301852489443442688 : ℝ))/216) (((21-5)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((33325770944820067/52216775542358336202495492096 : ℝ))/3) ((21-5)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((33325770944820067/52216775542358336202495492096 : ℝ))/36) (((21-5)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((33325770944820067/52216775542358336202495492096 : ℝ))/216) (((21-5)+2*14-5)+2) 1 14 A B))))))))

theorem boundaryImCoefficient77_5_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_5 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_5 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_5

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((-595134447329/45349632 : ℝ))/3) ((21-5)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-595134447329/45349632 : ℝ))/36) (((21-5)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-595134447329/45349632 : ℝ))/216) (((21-5)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((68246754478747/19591041024 : ℝ))/3) ((21-5)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((68246754478747/19591041024 : ℝ))/36) (((21-5)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((68246754478747/19591041024 : ℝ))/216) (((21-5)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-139280847775457/235092492288 : ℝ))/3) ((21-5)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-139280847775457/235092492288 : ℝ))/36) (((21-5)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-139280847775457/235092492288 : ℝ))/216) (((21-5)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-653806045063829/1586874322944 : ℝ))/3) ((21-5)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-653806045063829/1586874322944 : ℝ))/36) (((21-5)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-653806045063829/1586874322944 : ℝ))/216) (((21-5)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((576135055035147667/1828079220031488 : ℝ))/3) ((21-5)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((576135055035147667/1828079220031488 : ℝ))/36) (((21-5)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((576135055035147667/1828079220031488 : ℝ))/216) (((21-5)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-30144349061698426627/526486815369068544 : ℝ))/3) ((21-5)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-30144349061698426627/526486815369068544 : ℝ))/36) (((21-5)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-30144349061698426627/526486815369068544 : ℝ))/216) (((21-5)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((8535111205340920181/4211894522952548352 : ℝ))/3) ((21-5)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((8535111205340920181/4211894522952548352 : ℝ))/36) (((21-5)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((8535111205340920181/4211894522952548352 : ℝ))/216) (((21-5)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((87540653190844684615/113721152119718805504 : ℝ))/3) ((21-5)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((87540653190844684615/113721152119718805504 : ℝ))/36) (((21-5)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((87540653190844684615/113721152119718805504 : ℝ))/216) (((21-5)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-27755368091845695374635/196510150862874095910912 : ℝ))/3) ((21-5)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-27755368091845695374635/196510150862874095910912 : ℝ))/36) (((21-5)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-27755368091845695374635/196510150862874095910912 : ℝ))/216) (((21-5)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((6713613650610981410789/589530452588622287732736 : ℝ))/3) ((21-5)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((6713613650610981410789/589530452588622287732736 : ℝ))/36) (((21-5)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((6713613650610981410789/589530452588622287732736 : ℝ))/216) (((21-5)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1959259070331909946855/3979330554973200442195968 : ℝ))/3) ((21-5)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1959259070331909946855/3979330554973200442195968 : ℝ))/36) (((21-5)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1959259070331909946855/3979330554973200442195968 : ℝ))/216) (((21-5)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((701417487728543150753/71627949989517607959527424 : ℝ))/3) ((21-5)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((701417487728543150753/71627949989517607959527424 : ℝ))/36) (((21-5)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((701417487728543150753/71627949989517607959527424 : ℝ))/216) (((21-5)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-53871599646351098255/1289303099811316943271493632 : ℝ))/3) ((21-5)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-53871599646351098255/1289303099811316943271493632 : ℝ))/36) (((21-5)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-53871599646351098255/1289303099811316943271493632 : ℝ))/216) (((21-5)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2666267823376143329/11603727898301852489443442688 : ℝ))/3) ((21-5)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2666267823376143329/11603727898301852489443442688 : ℝ))/36) (((21-5)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2666267823376143329/11603727898301852489443442688 : ℝ))/216) (((21-5)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((33325770944820067/52216775542358336202495492096 : ℝ))/3) ((21-5)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((33325770944820067/52216775542358336202495492096 : ℝ))/36) (((21-5)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((33325770944820067/52216775542358336202495492096 : ℝ))/216) (((21-5)+2*14-5)+2) 1 14 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_5,boundaryZ77]

  ring


def boundaryImCoefficient77_6 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((-435529901581/30233088 : ℝ))/3) ((21-6)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((-435529901581/30233088 : ℝ))/36) (((21-6)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((-435529901581/30233088 : ℝ))/216) (((21-6)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((21079894651837/3265173504 : ℝ))/3) ((21-6)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((21079894651837/3265173504 : ℝ))/36) (((21-6)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((21079894651837/3265173504 : ℝ))/216) (((21-6)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((-9224477539639031/1410554953728 : ℝ))/3) ((21-6)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-9224477539639031/1410554953728 : ℝ))/36) (((21-6)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-9224477539639031/1410554953728 : ℝ))/216) (((21-6)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((124313652617230921/25389989167104 : ℝ))/3) ((21-6)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((124313652617230921/25389989167104 : ℝ))/36) (((21-6)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((124313652617230921/25389989167104 : ℝ))/216) (((21-6)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((-927716298309686179/1218719480020992 : ℝ))/3) ((21-6)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-927716298309686179/1218719480020992 : ℝ))/36) (((21-6)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-927716298309686179/1218719480020992 : ℝ))/216) (((21-6)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-33720799191539834227/526486815369068544 : ℝ))/3) ((21-6)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-33720799191539834227/526486815369068544 : ℝ))/36) (((21-6)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-33720799191539834227/526486815369068544 : ℝ))/216) (((21-6)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((1513072156662829446371/37907050706572935168 : ℝ))/3) ((21-6)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((1513072156662829446371/37907050706572935168 : ℝ))/36) (((21-6)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((1513072156662829446371/37907050706572935168 : ℝ))/216) (((21-6)+2*6-5)+2) 1 6 A B)))) + (((boundaryTermCoefficient77 (((-18092585090551991507689/2729307650873251332096 : ℝ))/3) ((21-6)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-18092585090551991507689/2729307650873251332096 : ℝ))/36) (((21-6)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-18092585090551991507689/2729307650873251332096 : ℝ))/216) (((21-6)+2*7-5)+2) 1 7 A B))))))) + ((((((boundaryTermCoefficient77 (((28957134332878925827015/49127537715718523977728 : ℝ))/3) ((21-6)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((28957134332878925827015/49127537715718523977728 : ℝ))/36) (((21-6)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((28957134332878925827015/49127537715718523977728 : ℝ))/216) (((21-6)+2*8-5)+2) 1 8 A B)))) + (((boundaryTermCoefficient77 (((-19521058616475826326175/589530452588622287732736 : ℝ))/3) ((21-6)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-19521058616475826326175/589530452588622287732736 : ℝ))/36) (((21-6)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-19521058616475826326175/589530452588622287732736 : ℝ))/216) (((21-6)+2*9-5)+2) 1 9 A B))))) + ((((boundaryTermCoefficient77 (((2685120561813462228287/1989665277486600221097984 : ℝ))/3) ((21-6)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((2685120561813462228287/1989665277486600221097984 : ℝ))/36) (((21-6)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((2685120561813462228287/1989665277486600221097984 : ℝ))/216) (((21-6)+2*10-5)+2) 1 10 A B)))) + (((boundaryTermCoefficient77 (((-2773143382194760538135/71627949989517607959527424 : ℝ))/3) ((21-6)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-2773143382194760538135/71627949989517607959527424 : ℝ))/36) (((21-6)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-2773143382194760538135/71627949989517607959527424 : ℝ))/216) (((21-6)+2*11-5)+2) 1 11 A B)))))) + (((((boundaryTermCoefficient77 (((3316585657773002819/6715120311517275746205696 : ℝ))/3) ((21-6)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((3316585657773002819/6715120311517275746205696 : ℝ))/36) (((21-6)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((3316585657773002819/6715120311517275746205696 : ℝ))/216) (((21-6)+2*12-5)+2) 1 12 A B)))) + (((boundaryTermCoefficient77 (((-18870706190402301557/11603727898301852489443442688 : ℝ))/3) ((21-6)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((-18870706190402301557/11603727898301852489443442688 : ℝ))/36) (((21-6)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((-18870706190402301557/11603727898301852489443442688 : ℝ))/216) (((21-6)+2*13-5)+2) 1 13 A B))))) + ((((boundaryTermCoefficient77 (((-7005682798896131/26108387771179168101247746048 : ℝ))/3) ((21-6)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((-7005682798896131/26108387771179168101247746048 : ℝ))/36) (((21-6)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((-7005682798896131/26108387771179168101247746048 : ℝ))/216) (((21-6)+2*14-5)+2) 1 14 A B)))) + (((boundaryTermCoefficient77 (((20228983537427/14685968121288282056951857152 : ℝ))/3) ((21-6)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((20228983537427/14685968121288282056951857152 : ℝ))/36) (((21-6)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((20228983537427/14685968121288282056951857152 : ℝ))/216) (((21-6)+2*15-5)+2) 1 15 A B))))))))

theorem boundaryImCoefficient77_6_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_6 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_6 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_6

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((-435529901581/30233088 : ℝ))/3) ((21-6)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-435529901581/30233088 : ℝ))/36) (((21-6)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-435529901581/30233088 : ℝ))/216) (((21-6)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((21079894651837/3265173504 : ℝ))/3) ((21-6)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((21079894651837/3265173504 : ℝ))/36) (((21-6)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((21079894651837/3265173504 : ℝ))/216) (((21-6)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-9224477539639031/1410554953728 : ℝ))/3) ((21-6)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-9224477539639031/1410554953728 : ℝ))/36) (((21-6)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-9224477539639031/1410554953728 : ℝ))/216) (((21-6)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((124313652617230921/25389989167104 : ℝ))/3) ((21-6)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((124313652617230921/25389989167104 : ℝ))/36) (((21-6)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((124313652617230921/25389989167104 : ℝ))/216) (((21-6)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-927716298309686179/1218719480020992 : ℝ))/3) ((21-6)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-927716298309686179/1218719480020992 : ℝ))/36) (((21-6)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-927716298309686179/1218719480020992 : ℝ))/216) (((21-6)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-33720799191539834227/526486815369068544 : ℝ))/3) ((21-6)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-33720799191539834227/526486815369068544 : ℝ))/36) (((21-6)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-33720799191539834227/526486815369068544 : ℝ))/216) (((21-6)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1513072156662829446371/37907050706572935168 : ℝ))/3) ((21-6)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1513072156662829446371/37907050706572935168 : ℝ))/36) (((21-6)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1513072156662829446371/37907050706572935168 : ℝ))/216) (((21-6)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-18092585090551991507689/2729307650873251332096 : ℝ))/3) ((21-6)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-18092585090551991507689/2729307650873251332096 : ℝ))/36) (((21-6)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-18092585090551991507689/2729307650873251332096 : ℝ))/216) (((21-6)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((28957134332878925827015/49127537715718523977728 : ℝ))/3) ((21-6)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((28957134332878925827015/49127537715718523977728 : ℝ))/36) (((21-6)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((28957134332878925827015/49127537715718523977728 : ℝ))/216) (((21-6)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-19521058616475826326175/589530452588622287732736 : ℝ))/3) ((21-6)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-19521058616475826326175/589530452588622287732736 : ℝ))/36) (((21-6)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-19521058616475826326175/589530452588622287732736 : ℝ))/216) (((21-6)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((2685120561813462228287/1989665277486600221097984 : ℝ))/3) ((21-6)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((2685120561813462228287/1989665277486600221097984 : ℝ))/36) (((21-6)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((2685120561813462228287/1989665277486600221097984 : ℝ))/216) (((21-6)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2773143382194760538135/71627949989517607959527424 : ℝ))/3) ((21-6)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2773143382194760538135/71627949989517607959527424 : ℝ))/36) (((21-6)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2773143382194760538135/71627949989517607959527424 : ℝ))/216) (((21-6)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((3316585657773002819/6715120311517275746205696 : ℝ))/3) ((21-6)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((3316585657773002819/6715120311517275746205696 : ℝ))/36) (((21-6)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((3316585657773002819/6715120311517275746205696 : ℝ))/216) (((21-6)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-18870706190402301557/11603727898301852489443442688 : ℝ))/3) ((21-6)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-18870706190402301557/11603727898301852489443442688 : ℝ))/36) (((21-6)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-18870706190402301557/11603727898301852489443442688 : ℝ))/216) (((21-6)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-7005682798896131/26108387771179168101247746048 : ℝ))/3) ((21-6)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-7005682798896131/26108387771179168101247746048 : ℝ))/36) (((21-6)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-7005682798896131/26108387771179168101247746048 : ℝ))/216) (((21-6)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((20228983537427/14685968121288282056951857152 : ℝ))/3) ((21-6)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((20228983537427/14685968121288282056951857152 : ℝ))/36) (((21-6)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((20228983537427/14685968121288282056951857152 : ℝ))/216) (((21-6)+2*15-5)+2) 1 15 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_6,boundaryZ77]

  ring


def boundaryImCoefficient77_7 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((6485976127/354294 : ℝ))/3) ((21-7)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((6485976127/354294 : ℝ))/36) (((21-7)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((6485976127/354294 : ℝ))/216) (((21-7)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((-1512397466611/51018336 : ℝ))/3) ((21-7)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((-1512397466611/51018336 : ℝ))/36) (((21-7)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((-1512397466611/51018336 : ℝ))/216) (((21-7)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((55906294622035723/1410554953728 : ℝ))/3) ((21-7)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((55906294622035723/1410554953728 : ℝ))/36) (((21-7)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((55906294622035723/1410554953728 : ℝ))/216) (((21-7)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((-93733933937039437/50779978334208 : ℝ))/3) ((21-7)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-93733933937039437/50779978334208 : ℝ))/36) (((21-7)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-93733933937039437/50779978334208 : ℝ))/216) (((21-7)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((-11873006041514127179/3656158440062976 : ℝ))/3) ((21-7)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-11873006041514127179/3656158440062976 : ℝ))/36) (((21-7)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-11873006041514127179/3656158440062976 : ℝ))/216) (((21-7)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((188763308079355258709/175495605123022848 : ℝ))/3) ((21-7)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((188763308079355258709/175495605123022848 : ℝ))/36) (((21-7)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((188763308079355258709/175495605123022848 : ℝ))/216) (((21-7)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((-1056501236337848358445/6317841784428822528 : ℝ))/3) ((21-7)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((-1056501236337848358445/6317841784428822528 : ℝ))/36) (((21-7)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((-1056501236337848358445/6317841784428822528 : ℝ))/216) (((21-7)+2*6-5)+2) 1 6 A B)))) + (((boundaryTermCoefficient77 (((34718044567770180348823/2729307650873251332096 : ℝ))/3) ((21-7)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((34718044567770180348823/2729307650873251332096 : ℝ))/36) (((21-7)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((34718044567770180348823/2729307650873251332096 : ℝ))/216) (((21-7)+2*7-5)+2) 1 7 A B))))))) + ((((((boundaryTermCoefficient77 (((-389889974090594344295/1535235553616203874304 : ℝ))/3) ((21-7)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-389889974090594344295/1535235553616203874304 : ℝ))/36) (((21-7)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-389889974090594344295/1535235553616203874304 : ℝ))/216) (((21-7)+2*8-5)+2) 1 8 A B)))) + (((boundaryTermCoefficient77 (((-14944578412970495446663/589530452588622287732736 : ℝ))/3) ((21-7)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-14944578412970495446663/589530452588622287732736 : ℝ))/36) (((21-7)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-14944578412970495446663/589530452588622287732736 : ℝ))/216) (((21-7)+2*9-5)+2) 1 9 A B))))) + ((((boundaryTermCoefficient77 (((1035895688294606674283/663221759162200073699328 : ℝ))/3) ((21-7)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((1035895688294606674283/663221759162200073699328 : ℝ))/36) (((21-7)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((1035895688294606674283/663221759162200073699328 : ℝ))/216) (((21-7)+2*10-5)+2) 1 10 A B)))) + (((boundaryTermCoefficient77 (((-52287251018809068667/3979330554973200442195968 : ℝ))/3) ((21-7)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-52287251018809068667/3979330554973200442195968 : ℝ))/36) (((21-7)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-52287251018809068667/3979330554973200442195968 : ℝ))/216) (((21-7)+2*11-5)+2) 1 11 A B)))))) + (((((boundaryTermCoefficient77 (((-13428613985746398665/23875983329839202653175808 : ℝ))/3) ((21-7)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-13428613985746398665/23875983329839202653175808 : ℝ))/36) (((21-7)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-13428613985746398665/23875983329839202653175808 : ℝ))/216) (((21-7)+2*12-5)+2) 1 12 A B)))) + (((boundaryTermCoefficient77 (((24801621332876898391/3867909299433950829814480896 : ℝ))/3) ((21-7)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((24801621332876898391/3867909299433950829814480896 : ℝ))/36) (((21-7)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((24801621332876898391/3867909299433950829814480896 : ℝ))/216) (((21-7)+2*13-5)+2) 1 13 A B))))) + ((((boundaryTermCoefficient77 (((-220215020591630995/17405591847452778734165164032 : ℝ))/3) ((21-7)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((-220215020591630995/17405591847452778734165164032 : ℝ))/36) (((21-7)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((-220215020591630995/17405591847452778734165164032 : ℝ))/216) (((21-7)+2*14-5)+2) 1 14 A B)))) + ((((boundaryTermCoefficient77 (((432407062850917/234975489940612512911229714432 : ℝ))/3) ((21-7)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((432407062850917/234975489940612512911229714432 : ℝ))/36) (((21-7)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((432407062850917/234975489940612512911229714432 : ℝ))/216) (((21-7)+2*15-5)+2) 1 15 A B)))) + (((boundaryTermCoefficient77 (((121763303179/264347426183189077025133428736 : ℝ))/3) ((21-7)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((121763303179/264347426183189077025133428736 : ℝ))/36) (((21-7)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((121763303179/264347426183189077025133428736 : ℝ))/216) (((21-7)+2*16-5)+2) 1 16 A B)))))))))

theorem boundaryImCoefficient77_7_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_7 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_7 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_7

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((6485976127/354294 : ℝ))/3) ((21-7)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((6485976127/354294 : ℝ))/36) (((21-7)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((6485976127/354294 : ℝ))/216) (((21-7)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1512397466611/51018336 : ℝ))/3) ((21-7)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1512397466611/51018336 : ℝ))/36) (((21-7)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1512397466611/51018336 : ℝ))/216) (((21-7)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((55906294622035723/1410554953728 : ℝ))/3) ((21-7)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((55906294622035723/1410554953728 : ℝ))/36) (((21-7)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((55906294622035723/1410554953728 : ℝ))/216) (((21-7)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-93733933937039437/50779978334208 : ℝ))/3) ((21-7)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-93733933937039437/50779978334208 : ℝ))/36) (((21-7)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-93733933937039437/50779978334208 : ℝ))/216) (((21-7)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-11873006041514127179/3656158440062976 : ℝ))/3) ((21-7)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-11873006041514127179/3656158440062976 : ℝ))/36) (((21-7)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-11873006041514127179/3656158440062976 : ℝ))/216) (((21-7)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((188763308079355258709/175495605123022848 : ℝ))/3) ((21-7)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((188763308079355258709/175495605123022848 : ℝ))/36) (((21-7)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((188763308079355258709/175495605123022848 : ℝ))/216) (((21-7)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1056501236337848358445/6317841784428822528 : ℝ))/3) ((21-7)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1056501236337848358445/6317841784428822528 : ℝ))/36) (((21-7)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1056501236337848358445/6317841784428822528 : ℝ))/216) (((21-7)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((34718044567770180348823/2729307650873251332096 : ℝ))/3) ((21-7)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((34718044567770180348823/2729307650873251332096 : ℝ))/36) (((21-7)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((34718044567770180348823/2729307650873251332096 : ℝ))/216) (((21-7)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-389889974090594344295/1535235553616203874304 : ℝ))/3) ((21-7)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-389889974090594344295/1535235553616203874304 : ℝ))/36) (((21-7)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-389889974090594344295/1535235553616203874304 : ℝ))/216) (((21-7)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-14944578412970495446663/589530452588622287732736 : ℝ))/3) ((21-7)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-14944578412970495446663/589530452588622287732736 : ℝ))/36) (((21-7)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-14944578412970495446663/589530452588622287732736 : ℝ))/216) (((21-7)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1035895688294606674283/663221759162200073699328 : ℝ))/3) ((21-7)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1035895688294606674283/663221759162200073699328 : ℝ))/36) (((21-7)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1035895688294606674283/663221759162200073699328 : ℝ))/216) (((21-7)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-52287251018809068667/3979330554973200442195968 : ℝ))/3) ((21-7)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-52287251018809068667/3979330554973200442195968 : ℝ))/36) (((21-7)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-52287251018809068667/3979330554973200442195968 : ℝ))/216) (((21-7)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-13428613985746398665/23875983329839202653175808 : ℝ))/3) ((21-7)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-13428613985746398665/23875983329839202653175808 : ℝ))/36) (((21-7)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-13428613985746398665/23875983329839202653175808 : ℝ))/216) (((21-7)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((24801621332876898391/3867909299433950829814480896 : ℝ))/3) ((21-7)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((24801621332876898391/3867909299433950829814480896 : ℝ))/36) (((21-7)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((24801621332876898391/3867909299433950829814480896 : ℝ))/216) (((21-7)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-220215020591630995/17405591847452778734165164032 : ℝ))/3) ((21-7)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-220215020591630995/17405591847452778734165164032 : ℝ))/36) (((21-7)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-220215020591630995/17405591847452778734165164032 : ℝ))/216) (((21-7)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((432407062850917/234975489940612512911229714432 : ℝ))/3) ((21-7)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((432407062850917/234975489940612512911229714432 : ℝ))/36) (((21-7)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((432407062850917/234975489940612512911229714432 : ℝ))/216) (((21-7)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((121763303179/264347426183189077025133428736 : ℝ))/3) ((21-7)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((121763303179/264347426183189077025133428736 : ℝ))/36) (((21-7)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((121763303179/264347426183189077025133428736 : ℝ))/216) (((21-7)+2*16-5)+2) 1 16 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_7,boundaryZ77]

  ring


def boundaryImCoefficient77_8 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((12527514121/2834352 : ℝ))/3) ((21-8)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((12527514121/2834352 : ℝ))/36) (((21-8)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((12527514121/2834352 : ℝ))/216) (((21-8)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((103937121884549/612220032 : ℝ))/3) ((21-8)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((103937121884549/612220032 : ℝ))/36) (((21-8)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((103937121884549/612220032 : ℝ))/216) (((21-8)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((22103980013276113/352638738432 : ℝ))/3) ((21-8)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((22103980013276113/352638738432 : ℝ))/36) (((21-8)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((22103980013276113/352638738432 : ℝ))/216) (((21-8)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((-2764061372084054567/50779978334208 : ℝ))/3) ((21-8)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-2764061372084054567/50779978334208 : ℝ))/36) (((21-8)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-2764061372084054567/50779978334208 : ℝ))/216) (((21-8)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((112996085825195544631/7312316880125952 : ℝ))/3) ((21-8)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((112996085825195544631/7312316880125952 : ℝ))/36) (((21-8)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((112996085825195544631/7312316880125952 : ℝ))/216) (((21-8)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-1152414434751891020869/526486815369068544 : ℝ))/3) ((21-8)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-1152414434751891020869/526486815369068544 : ℝ))/36) (((21-8)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-1152414434751891020869/526486815369068544 : ℝ))/216) (((21-8)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((666591430340066365967/12635683568857645056 : ℝ))/3) ((21-8)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((666591430340066365967/12635683568857645056 : ℝ))/36) (((21-8)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((666591430340066365967/12635683568857645056 : ℝ))/216) (((21-8)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((40719454819020256086709/1364653825436625666048 : ℝ))/3) ((21-8)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((40719454819020256086709/1364653825436625666048 : ℝ))/36) (((21-8)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((40719454819020256086709/1364653825436625666048 : ℝ))/216) (((21-8)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((-232348310570295420515159/49127537715718523977728 : ℝ))/3) ((21-8)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-232348310570295420515159/49127537715718523977728 : ℝ))/36) (((21-8)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-232348310570295420515159/49127537715718523977728 : ℝ))/216) (((21-8)+2*8-5)+2) 1 8 A B)))))))) + ((((((boundaryTermCoefficient77 (((25688294525482570044535/73691306573577785966592 : ℝ))/3) ((21-8)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((25688294525482570044535/73691306573577785966592 : ℝ))/36) (((21-8)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((25688294525482570044535/73691306573577785966592 : ℝ))/216) (((21-8)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((-116728468063016088656663/7958661109946400884391936 : ℝ))/3) ((21-8)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((-116728468063016088656663/7958661109946400884391936 : ℝ))/36) (((21-8)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((-116728468063016088656663/7958661109946400884391936 : ℝ))/216) (((21-8)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((2698262661898301017619/7958661109946400884391936 : ℝ))/3) ((21-8)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((2698262661898301017619/7958661109946400884391936 : ℝ))/36) (((21-8)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((2698262661898301017619/7958661109946400884391936 : ℝ))/216) (((21-8)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((-667928938946074571671/214883849968552823878582272 : ℝ))/3) ((21-8)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-667928938946074571671/214883849968552823878582272 : ℝ))/36) (((21-8)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-667928938946074571671/214883849968552823878582272 : ℝ))/216) (((21-8)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((9061942056114367711/1933954649716975414907240448 : ℝ))/3) ((21-8)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((9061942056114367711/1933954649716975414907240448 : ℝ))/36) (((21-8)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((9061942056114367711/1933954649716975414907240448 : ℝ))/216) (((21-8)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((518578544687791259/26108387771179168101247746048 : ℝ))/3) ((21-8)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((518578544687791259/26108387771179168101247746048 : ℝ))/36) (((21-8)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((518578544687791259/26108387771179168101247746048 : ℝ))/216) (((21-8)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((-83858433492463/3671492030322070514237964288 : ℝ))/3) ((21-8)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((-83858433492463/3671492030322070514237964288 : ℝ))/36) (((21-8)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((-83858433492463/3671492030322070514237964288 : ℝ))/216) (((21-8)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((99107635249/88115808727729692341711142912 : ℝ))/3) ((21-8)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((99107635249/88115808727729692341711142912 : ℝ))/36) (((21-8)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((99107635249/88115808727729692341711142912 : ℝ))/216) (((21-8)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((-5764801/148695427228043855826637553664 : ℝ))/3) ((21-8)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((-5764801/148695427228043855826637553664 : ℝ))/36) (((21-8)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((-5764801/148695427228043855826637553664 : ℝ))/216) (((21-8)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_8_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_8 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_8 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_8

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((12527514121/2834352 : ℝ))/3) ((21-8)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((12527514121/2834352 : ℝ))/36) (((21-8)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((12527514121/2834352 : ℝ))/216) (((21-8)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((103937121884549/612220032 : ℝ))/3) ((21-8)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((103937121884549/612220032 : ℝ))/36) (((21-8)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((103937121884549/612220032 : ℝ))/216) (((21-8)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((22103980013276113/352638738432 : ℝ))/3) ((21-8)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((22103980013276113/352638738432 : ℝ))/36) (((21-8)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((22103980013276113/352638738432 : ℝ))/216) (((21-8)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2764061372084054567/50779978334208 : ℝ))/3) ((21-8)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2764061372084054567/50779978334208 : ℝ))/36) (((21-8)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2764061372084054567/50779978334208 : ℝ))/216) (((21-8)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((112996085825195544631/7312316880125952 : ℝ))/3) ((21-8)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((112996085825195544631/7312316880125952 : ℝ))/36) (((21-8)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((112996085825195544631/7312316880125952 : ℝ))/216) (((21-8)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1152414434751891020869/526486815369068544 : ℝ))/3) ((21-8)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1152414434751891020869/526486815369068544 : ℝ))/36) (((21-8)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1152414434751891020869/526486815369068544 : ℝ))/216) (((21-8)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((666591430340066365967/12635683568857645056 : ℝ))/3) ((21-8)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((666591430340066365967/12635683568857645056 : ℝ))/36) (((21-8)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((666591430340066365967/12635683568857645056 : ℝ))/216) (((21-8)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((40719454819020256086709/1364653825436625666048 : ℝ))/3) ((21-8)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((40719454819020256086709/1364653825436625666048 : ℝ))/36) (((21-8)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((40719454819020256086709/1364653825436625666048 : ℝ))/216) (((21-8)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-232348310570295420515159/49127537715718523977728 : ℝ))/3) ((21-8)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-232348310570295420515159/49127537715718523977728 : ℝ))/36) (((21-8)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-232348310570295420515159/49127537715718523977728 : ℝ))/216) (((21-8)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((25688294525482570044535/73691306573577785966592 : ℝ))/3) ((21-8)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((25688294525482570044535/73691306573577785966592 : ℝ))/36) (((21-8)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((25688294525482570044535/73691306573577785966592 : ℝ))/216) (((21-8)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-116728468063016088656663/7958661109946400884391936 : ℝ))/3) ((21-8)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-116728468063016088656663/7958661109946400884391936 : ℝ))/36) (((21-8)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-116728468063016088656663/7958661109946400884391936 : ℝ))/216) (((21-8)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((2698262661898301017619/7958661109946400884391936 : ℝ))/3) ((21-8)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((2698262661898301017619/7958661109946400884391936 : ℝ))/36) (((21-8)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((2698262661898301017619/7958661109946400884391936 : ℝ))/216) (((21-8)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-667928938946074571671/214883849968552823878582272 : ℝ))/3) ((21-8)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-667928938946074571671/214883849968552823878582272 : ℝ))/36) (((21-8)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-667928938946074571671/214883849968552823878582272 : ℝ))/216) (((21-8)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((9061942056114367711/1933954649716975414907240448 : ℝ))/3) ((21-8)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((9061942056114367711/1933954649716975414907240448 : ℝ))/36) (((21-8)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((9061942056114367711/1933954649716975414907240448 : ℝ))/216) (((21-8)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((518578544687791259/26108387771179168101247746048 : ℝ))/3) ((21-8)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((518578544687791259/26108387771179168101247746048 : ℝ))/36) (((21-8)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((518578544687791259/26108387771179168101247746048 : ℝ))/216) (((21-8)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-83858433492463/3671492030322070514237964288 : ℝ))/3) ((21-8)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-83858433492463/3671492030322070514237964288 : ℝ))/36) (((21-8)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-83858433492463/3671492030322070514237964288 : ℝ))/216) (((21-8)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((99107635249/88115808727729692341711142912 : ℝ))/3) ((21-8)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((99107635249/88115808727729692341711142912 : ℝ))/36) (((21-8)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((99107635249/88115808727729692341711142912 : ℝ))/216) (((21-8)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-5764801/148695427228043855826637553664 : ℝ))/3) ((21-8)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-5764801/148695427228043855826637553664 : ℝ))/36) (((21-8)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-5764801/148695427228043855826637553664 : ℝ))/216) (((21-8)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_8,boundaryZ77]

  ring


def boundaryImCoefficient77_9 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((883107573397/2125764 : ℝ))/3) ((21-9)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((883107573397/2125764 : ℝ))/36) (((21-9)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((883107573397/2125764 : ℝ))/216) (((21-9)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((33041956144873/51018336 : ℝ))/3) ((21-9)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((33041956144873/51018336 : ℝ))/36) (((21-9)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((33041956144873/51018336 : ℝ))/216) (((21-9)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((-275023540930675933/705277476864 : ℝ))/3) ((21-9)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-275023540930675933/705277476864 : ℝ))/36) (((21-9)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-275023540930675933/705277476864 : ℝ))/216) (((21-9)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((4896217808561804567/50779978334208 : ℝ))/3) ((21-9)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((4896217808561804567/50779978334208 : ℝ))/36) (((21-9)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((4896217808561804567/50779978334208 : ℝ))/216) (((21-9)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((-7877649846144796109/1218719480020992 : ℝ))/3) ((21-9)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-7877649846144796109/1218719480020992 : ℝ))/36) (((21-9)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-7877649846144796109/1218719480020992 : ℝ))/216) (((21-9)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-527453930303400479755/131621703842267136 : ℝ))/3) ((21-9)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-527453930303400479755/131621703842267136 : ℝ))/36) (((21-9)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-527453930303400479755/131621703842267136 : ℝ))/216) (((21-9)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((12458970774516295731425/9476762676643233792 : ℝ))/3) ((21-9)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((12458970774516295731425/9476762676643233792 : ℝ))/36) (((21-9)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((12458970774516295731425/9476762676643233792 : ℝ))/216) (((21-9)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((-24349283258521101697/131621703842267136 : ℝ))/3) ((21-9)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-24349283258521101697/131621703842267136 : ℝ))/36) (((21-9)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-24349283258521101697/131621703842267136 : ℝ))/216) (((21-9)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((90695834307067983738521/6140942214464815497216 : ℝ))/3) ((21-9)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((90695834307067983738521/6140942214464815497216 : ℝ))/36) (((21-9)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((90695834307067983738521/6140942214464815497216 : ℝ))/216) (((21-9)+2*8-5)+2) 1 8 A B)))))))) + ((((((boundaryTermCoefficient77 (((-109572784178532326192639/147382613147155571933184 : ℝ))/3) ((21-9)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-109572784178532326192639/147382613147155571933184 : ℝ))/36) (((21-9)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-109572784178532326192639/147382613147155571933184 : ℝ))/216) (((21-9)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((34450895411528530056647/1326443518324400147398656 : ℝ))/3) ((21-9)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((34450895411528530056647/1326443518324400147398656 : ℝ))/36) (((21-9)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((34450895411528530056647/1326443518324400147398656 : ℝ))/216) (((21-9)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((-7912579175518822931677/11937991664919601326587904 : ℝ))/3) ((21-9)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-7912579175518822931677/11937991664919601326587904 : ℝ))/36) (((21-9)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-7912579175518822931677/11937991664919601326587904 : ℝ))/216) (((21-9)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((64669213170180283487/6715120311517275746205696 : ℝ))/3) ((21-9)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((64669213170180283487/6715120311517275746205696 : ℝ))/36) (((21-9)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((64669213170180283487/6715120311517275746205696 : ℝ))/216) (((21-9)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((-50458074112147463491/966977324858487707453620224 : ℝ))/3) ((21-9)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((-50458074112147463491/966977324858487707453620224 : ℝ))/36) (((21-9)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((-50458074112147463491/966977324858487707453620224 : ℝ))/216) (((21-9)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((614700438185525405/8702795923726389367082582016 : ℝ))/3) ((21-9)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((614700438185525405/8702795923726389367082582016 : ℝ))/36) (((21-9)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((614700438185525405/8702795923726389367082582016 : ℝ))/216) (((21-9)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((311279414855647/78325163313537504303743238144 : ℝ))/3) ((21-9)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((311279414855647/78325163313537504303743238144 : ℝ))/36) (((21-9)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((311279414855647/78325163313537504303743238144 : ℝ))/216) (((21-9)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((-1010051842051/176231617455459384683422285824 : ℝ))/3) ((21-9)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((-1010051842051/176231617455459384683422285824 : ℝ))/36) (((21-9)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((-1010051842051/176231617455459384683422285824 : ℝ))/216) (((21-9)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((-45294865/198260569637391807768850071552 : ℝ))/3) ((21-9)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((-45294865/198260569637391807768850071552 : ℝ))/36) (((21-9)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((-45294865/198260569637391807768850071552 : ℝ))/216) (((21-9)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_9_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_9 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_9 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_9

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((883107573397/2125764 : ℝ))/3) ((21-9)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((883107573397/2125764 : ℝ))/36) (((21-9)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((883107573397/2125764 : ℝ))/216) (((21-9)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((33041956144873/51018336 : ℝ))/3) ((21-9)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((33041956144873/51018336 : ℝ))/36) (((21-9)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((33041956144873/51018336 : ℝ))/216) (((21-9)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-275023540930675933/705277476864 : ℝ))/3) ((21-9)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-275023540930675933/705277476864 : ℝ))/36) (((21-9)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-275023540930675933/705277476864 : ℝ))/216) (((21-9)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((4896217808561804567/50779978334208 : ℝ))/3) ((21-9)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((4896217808561804567/50779978334208 : ℝ))/36) (((21-9)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((4896217808561804567/50779978334208 : ℝ))/216) (((21-9)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-7877649846144796109/1218719480020992 : ℝ))/3) ((21-9)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-7877649846144796109/1218719480020992 : ℝ))/36) (((21-9)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-7877649846144796109/1218719480020992 : ℝ))/216) (((21-9)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-527453930303400479755/131621703842267136 : ℝ))/3) ((21-9)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-527453930303400479755/131621703842267136 : ℝ))/36) (((21-9)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-527453930303400479755/131621703842267136 : ℝ))/216) (((21-9)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((12458970774516295731425/9476762676643233792 : ℝ))/3) ((21-9)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((12458970774516295731425/9476762676643233792 : ℝ))/36) (((21-9)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((12458970774516295731425/9476762676643233792 : ℝ))/216) (((21-9)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-24349283258521101697/131621703842267136 : ℝ))/3) ((21-9)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-24349283258521101697/131621703842267136 : ℝ))/36) (((21-9)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-24349283258521101697/131621703842267136 : ℝ))/216) (((21-9)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((90695834307067983738521/6140942214464815497216 : ℝ))/3) ((21-9)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((90695834307067983738521/6140942214464815497216 : ℝ))/36) (((21-9)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((90695834307067983738521/6140942214464815497216 : ℝ))/216) (((21-9)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-109572784178532326192639/147382613147155571933184 : ℝ))/3) ((21-9)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-109572784178532326192639/147382613147155571933184 : ℝ))/36) (((21-9)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-109572784178532326192639/147382613147155571933184 : ℝ))/216) (((21-9)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((34450895411528530056647/1326443518324400147398656 : ℝ))/3) ((21-9)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((34450895411528530056647/1326443518324400147398656 : ℝ))/36) (((21-9)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((34450895411528530056647/1326443518324400147398656 : ℝ))/216) (((21-9)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-7912579175518822931677/11937991664919601326587904 : ℝ))/3) ((21-9)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-7912579175518822931677/11937991664919601326587904 : ℝ))/36) (((21-9)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-7912579175518822931677/11937991664919601326587904 : ℝ))/216) (((21-9)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((64669213170180283487/6715120311517275746205696 : ℝ))/3) ((21-9)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((64669213170180283487/6715120311517275746205696 : ℝ))/36) (((21-9)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((64669213170180283487/6715120311517275746205696 : ℝ))/216) (((21-9)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-50458074112147463491/966977324858487707453620224 : ℝ))/3) ((21-9)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-50458074112147463491/966977324858487707453620224 : ℝ))/36) (((21-9)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-50458074112147463491/966977324858487707453620224 : ℝ))/216) (((21-9)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((614700438185525405/8702795923726389367082582016 : ℝ))/3) ((21-9)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((614700438185525405/8702795923726389367082582016 : ℝ))/36) (((21-9)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((614700438185525405/8702795923726389367082582016 : ℝ))/216) (((21-9)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((311279414855647/78325163313537504303743238144 : ℝ))/3) ((21-9)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((311279414855647/78325163313537504303743238144 : ℝ))/36) (((21-9)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((311279414855647/78325163313537504303743238144 : ℝ))/216) (((21-9)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1010051842051/176231617455459384683422285824 : ℝ))/3) ((21-9)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1010051842051/176231617455459384683422285824 : ℝ))/36) (((21-9)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1010051842051/176231617455459384683422285824 : ℝ))/216) (((21-9)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-45294865/198260569637391807768850071552 : ℝ))/3) ((21-9)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-45294865/198260569637391807768850071552 : ℝ))/36) (((21-9)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-45294865/198260569637391807768850071552 : ℝ))/216) (((21-9)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_9,boundaryZ77]

  ring


def boundaryImCoefficient77_10 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((1056981749179/531441 : ℝ))/3) ((21-10)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((1056981749179/531441 : ℝ))/36) (((21-10)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((1056981749179/531441 : ℝ))/216) (((21-10)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((-11402695394645/12754584 : ℝ))/3) ((21-10)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((-11402695394645/12754584 : ℝ))/36) (((21-10)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((-11402695394645/12754584 : ℝ))/216) (((21-10)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((12870230893791391/470184984576 : ℝ))/3) ((21-10)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((12870230893791391/470184984576 : ℝ))/36) (((21-10)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((12870230893791391/470184984576 : ℝ))/216) (((21-10)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((7361937210697033783/50779978334208 : ℝ))/3) ((21-10)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((7361937210697033783/50779978334208 : ℝ))/36) (((21-10)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((7361937210697033783/50779978334208 : ℝ))/216) (((21-10)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((-21005958712237110757/228509902503936 : ℝ))/3) ((21-10)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-21005958712237110757/228509902503936 : ℝ))/36) (((21-10)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-21005958712237110757/228509902503936 : ℝ))/216) (((21-10)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((277597856591286462035/10968475320188928 : ℝ))/3) ((21-10)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((277597856591286462035/10968475320188928 : ℝ))/36) (((21-10)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((277597856591286462035/10968475320188928 : ℝ))/216) (((21-10)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((-8689755945636813856739/2369190669160808448 : ℝ))/3) ((21-10)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((-8689755945636813856739/2369190669160808448 : ℝ))/36) (((21-10)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((-8689755945636813856739/2369190669160808448 : ℝ))/216) (((21-10)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((25228436644955969253769/85290864089789104128 : ℝ))/3) ((21-10)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((25228436644955969253769/85290864089789104128 : ℝ))/36) (((21-10)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((25228436644955969253769/85290864089789104128 : ℝ))/216) (((21-10)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((-51781920294494115701321/4093961476309876998144 : ℝ))/3) ((21-10)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-51781920294494115701321/4093961476309876998144 : ℝ))/36) (((21-10)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-51781920294494115701321/4093961476309876998144 : ℝ))/216) (((21-10)+2*8-5)+2) 1 8 A B)))))))) + ((((((boundaryTermCoefficient77 (((22116772737772060641623/110536959860366678949888 : ℝ))/3) ((21-10)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((22116772737772060641623/110536959860366678949888 : ℝ))/36) (((21-10)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((22116772737772060641623/110536959860366678949888 : ℝ))/216) (((21-10)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((5381776536547254490367/1989665277486600221097984 : ℝ))/3) ((21-10)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((5381776536547254490367/1989665277486600221097984 : ℝ))/36) (((21-10)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((5381776536547254490367/1989665277486600221097984 : ℝ))/216) (((21-10)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((-2461295950530559967/497416319371650055274496 : ℝ))/3) ((21-10)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-2461295950530559967/497416319371650055274496 : ℝ))/36) (((21-10)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-2461295950530559967/497416319371650055274496 : ℝ))/216) (((21-10)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((-286583397345662596295/53720962492138205969645568 : ℝ))/3) ((21-10)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-286583397345662596295/53720962492138205969645568 : ℝ))/36) (((21-10)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-286583397345662596295/53720962492138205969645568 : ℝ))/216) (((21-10)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((35277275277781064663/483488662429243853726810112 : ℝ))/3) ((21-10)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((35277275277781064663/483488662429243853726810112 : ℝ))/36) (((21-10)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((35277275277781064663/483488662429243853726810112 : ℝ))/216) (((21-10)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((-3045337463733407/13430240623034551492411392 : ℝ))/3) ((21-10)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((-3045337463733407/13430240623034551492411392 : ℝ))/36) (((21-10)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((-3045337463733407/13430240623034551492411392 : ℝ))/216) (((21-10)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((5692246506325295/39162581656768752151871619072 : ℝ))/3) ((21-10)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((5692246506325295/39162581656768752151871619072 : ℝ))/36) (((21-10)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((5692246506325295/39162581656768752151871619072 : ℝ))/216) (((21-10)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((-43152392675/9790645414192188037967904768 : ℝ))/3) ((21-10)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((-43152392675/9790645414192188037967904768 : ℝ))/36) (((21-10)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((-43152392675/9790645414192188037967904768 : ℝ))/216) (((21-10)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((823543/5507238045483105771356946432 : ℝ))/3) ((21-10)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((823543/5507238045483105771356946432 : ℝ))/36) (((21-10)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((823543/5507238045483105771356946432 : ℝ))/216) (((21-10)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_10_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_10 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_10 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_10

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((1056981749179/531441 : ℝ))/3) ((21-10)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1056981749179/531441 : ℝ))/36) (((21-10)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1056981749179/531441 : ℝ))/216) (((21-10)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-11402695394645/12754584 : ℝ))/3) ((21-10)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-11402695394645/12754584 : ℝ))/36) (((21-10)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-11402695394645/12754584 : ℝ))/216) (((21-10)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((12870230893791391/470184984576 : ℝ))/3) ((21-10)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((12870230893791391/470184984576 : ℝ))/36) (((21-10)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((12870230893791391/470184984576 : ℝ))/216) (((21-10)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((7361937210697033783/50779978334208 : ℝ))/3) ((21-10)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((7361937210697033783/50779978334208 : ℝ))/36) (((21-10)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((7361937210697033783/50779978334208 : ℝ))/216) (((21-10)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-21005958712237110757/228509902503936 : ℝ))/3) ((21-10)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-21005958712237110757/228509902503936 : ℝ))/36) (((21-10)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-21005958712237110757/228509902503936 : ℝ))/216) (((21-10)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((277597856591286462035/10968475320188928 : ℝ))/3) ((21-10)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((277597856591286462035/10968475320188928 : ℝ))/36) (((21-10)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((277597856591286462035/10968475320188928 : ℝ))/216) (((21-10)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-8689755945636813856739/2369190669160808448 : ℝ))/3) ((21-10)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-8689755945636813856739/2369190669160808448 : ℝ))/36) (((21-10)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-8689755945636813856739/2369190669160808448 : ℝ))/216) (((21-10)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((25228436644955969253769/85290864089789104128 : ℝ))/3) ((21-10)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((25228436644955969253769/85290864089789104128 : ℝ))/36) (((21-10)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((25228436644955969253769/85290864089789104128 : ℝ))/216) (((21-10)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-51781920294494115701321/4093961476309876998144 : ℝ))/3) ((21-10)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-51781920294494115701321/4093961476309876998144 : ℝ))/36) (((21-10)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-51781920294494115701321/4093961476309876998144 : ℝ))/216) (((21-10)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((22116772737772060641623/110536959860366678949888 : ℝ))/3) ((21-10)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((22116772737772060641623/110536959860366678949888 : ℝ))/36) (((21-10)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((22116772737772060641623/110536959860366678949888 : ℝ))/216) (((21-10)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((5381776536547254490367/1989665277486600221097984 : ℝ))/3) ((21-10)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((5381776536547254490367/1989665277486600221097984 : ℝ))/36) (((21-10)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((5381776536547254490367/1989665277486600221097984 : ℝ))/216) (((21-10)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2461295950530559967/497416319371650055274496 : ℝ))/3) ((21-10)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2461295950530559967/497416319371650055274496 : ℝ))/36) (((21-10)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2461295950530559967/497416319371650055274496 : ℝ))/216) (((21-10)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-286583397345662596295/53720962492138205969645568 : ℝ))/3) ((21-10)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-286583397345662596295/53720962492138205969645568 : ℝ))/36) (((21-10)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-286583397345662596295/53720962492138205969645568 : ℝ))/216) (((21-10)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((35277275277781064663/483488662429243853726810112 : ℝ))/3) ((21-10)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((35277275277781064663/483488662429243853726810112 : ℝ))/36) (((21-10)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((35277275277781064663/483488662429243853726810112 : ℝ))/216) (((21-10)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-3045337463733407/13430240623034551492411392 : ℝ))/3) ((21-10)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-3045337463733407/13430240623034551492411392 : ℝ))/36) (((21-10)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-3045337463733407/13430240623034551492411392 : ℝ))/216) (((21-10)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((5692246506325295/39162581656768752151871619072 : ℝ))/3) ((21-10)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((5692246506325295/39162581656768752151871619072 : ℝ))/36) (((21-10)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((5692246506325295/39162581656768752151871619072 : ℝ))/216) (((21-10)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-43152392675/9790645414192188037967904768 : ℝ))/3) ((21-10)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-43152392675/9790645414192188037967904768 : ℝ))/36) (((21-10)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-43152392675/9790645414192188037967904768 : ℝ))/216) (((21-10)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((823543/5507238045483105771356946432 : ℝ))/3) ((21-10)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((823543/5507238045483105771356946432 : ℝ))/36) (((21-10)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((823543/5507238045483105771356946432 : ℝ))/216) (((21-10)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_10,boundaryZ77]

  ring


def boundaryImCoefficient77_11 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((387862448546/531441 : ℝ))/3) ((21-11)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((387862448546/531441 : ℝ))/36) (((21-11)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((387862448546/531441 : ℝ))/216) (((21-11)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((-1840027141589/1062882 : ℝ))/3) ((21-11)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((-1840027141589/1062882 : ℝ))/36) (((21-11)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((-1840027141589/1062882 : ℝ))/216) (((21-11)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((647159530264634513/470184984576 : ℝ))/3) ((21-11)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((647159530264634513/470184984576 : ℝ))/36) (((21-11)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((647159530264634513/470184984576 : ℝ))/216) (((21-11)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((-6917532202939476529/8463329722368 : ℝ))/3) ((21-11)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-6917532202939476529/8463329722368 : ℝ))/36) (((21-11)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-6917532202939476529/8463329722368 : ℝ))/216) (((21-11)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((882016326540022631215/3656158440062976 : ℝ))/3) ((21-11)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((882016326540022631215/3656158440062976 : ℝ))/36) (((21-11)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((882016326540022631215/3656158440062976 : ℝ))/216) (((21-11)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-4545390810138934654915/131621703842267136 : ℝ))/3) ((21-11)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-4545390810138934654915/131621703842267136 : ℝ))/36) (((21-11)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-4545390810138934654915/131621703842267136 : ℝ))/216) (((21-11)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((1439110332312322964399/789730223053602816 : ℝ))/3) ((21-11)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((1439110332312322964399/789730223053602816 : ℝ))/36) (((21-11)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((1439110332312322964399/789730223053602816 : ℝ))/216) (((21-11)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((11486925271511345542985/85290864089789104128 : ℝ))/3) ((21-11)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((11486925271511345542985/85290864089789104128 : ℝ))/36) (((21-11)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((11486925271511345542985/85290864089789104128 : ℝ))/216) (((21-11)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((-177667019376837771900037/6140942214464815497216 : ℝ))/3) ((21-11)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-177667019376837771900037/6140942214464815497216 : ℝ))/36) (((21-11)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-177667019376837771900037/6140942214464815497216 : ℝ))/216) (((21-11)+2*8-5)+2) 1 8 A B)))))))) + ((((((boundaryTermCoefficient77 (((30116181184398691347919/13817119982545834868736 : ℝ))/3) ((21-11)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((30116181184398691347919/13817119982545834868736 : ℝ))/36) (((21-11)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((30116181184398691347919/13817119982545834868736 : ℝ))/216) (((21-11)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((-11290153506474494427131/124354079842912513818624 : ℝ))/3) ((21-11)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((-11290153506474494427131/124354079842912513818624 : ℝ))/36) (((21-11)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((-11290153506474494427131/124354079842912513818624 : ℝ))/216) (((21-11)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((18890139867475262663467/8953493748689700994940928 : ℝ))/3) ((21-11)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((18890139867475262663467/8953493748689700994940928 : ℝ))/36) (((21-11)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((18890139867475262663467/8953493748689700994940928 : ℝ))/216) (((21-11)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((-578781432778087876871/26860481246069102984822784 : ℝ))/3) ((21-11)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-578781432778087876871/26860481246069102984822784 : ℝ))/36) (((21-11)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-578781432778087876871/26860481246069102984822784 : ℝ))/216) (((21-11)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((70339605743459581/1259085058409489202413568 : ℝ))/3) ((21-11)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((70339605743459581/1259085058409489202413568 : ℝ))/36) (((21-11)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((70339605743459581/1259085058409489202413568 : ℝ))/216) (((21-11)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((100939973621334535/1087849490465798670885322752 : ℝ))/3) ((21-11)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((100939973621334535/1087849490465798670885322752 : ℝ))/36) (((21-11)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((100939973621334535/1087849490465798670885322752 : ℝ))/216) (((21-11)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((-1470496489030303/6527096942794792025311936512 : ℝ))/3) ((21-11)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((-1470496489030303/6527096942794792025311936512 : ℝ))/36) (((21-11)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((-1470496489030303/6527096942794792025311936512 : ℝ))/216) (((21-11)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((70124631227/2175698980931597341770645504 : ℝ))/3) ((21-11)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((70124631227/2175698980931597341770645504 : ℝ))/36) (((21-11)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((70124631227/2175698980931597341770645504 : ℝ))/216) (((21-11)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((24118045/11014476090966211542713892864 : ℝ))/3) ((21-11)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((24118045/11014476090966211542713892864 : ℝ))/36) (((21-11)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((24118045/11014476090966211542713892864 : ℝ))/216) (((21-11)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_11_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_11 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_11 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_11

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((387862448546/531441 : ℝ))/3) ((21-11)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((387862448546/531441 : ℝ))/36) (((21-11)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((387862448546/531441 : ℝ))/216) (((21-11)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1840027141589/1062882 : ℝ))/3) ((21-11)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1840027141589/1062882 : ℝ))/36) (((21-11)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1840027141589/1062882 : ℝ))/216) (((21-11)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((647159530264634513/470184984576 : ℝ))/3) ((21-11)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((647159530264634513/470184984576 : ℝ))/36) (((21-11)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((647159530264634513/470184984576 : ℝ))/216) (((21-11)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-6917532202939476529/8463329722368 : ℝ))/3) ((21-11)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-6917532202939476529/8463329722368 : ℝ))/36) (((21-11)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-6917532202939476529/8463329722368 : ℝ))/216) (((21-11)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((882016326540022631215/3656158440062976 : ℝ))/3) ((21-11)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((882016326540022631215/3656158440062976 : ℝ))/36) (((21-11)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((882016326540022631215/3656158440062976 : ℝ))/216) (((21-11)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-4545390810138934654915/131621703842267136 : ℝ))/3) ((21-11)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-4545390810138934654915/131621703842267136 : ℝ))/36) (((21-11)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-4545390810138934654915/131621703842267136 : ℝ))/216) (((21-11)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1439110332312322964399/789730223053602816 : ℝ))/3) ((21-11)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1439110332312322964399/789730223053602816 : ℝ))/36) (((21-11)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1439110332312322964399/789730223053602816 : ℝ))/216) (((21-11)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((11486925271511345542985/85290864089789104128 : ℝ))/3) ((21-11)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((11486925271511345542985/85290864089789104128 : ℝ))/36) (((21-11)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((11486925271511345542985/85290864089789104128 : ℝ))/216) (((21-11)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-177667019376837771900037/6140942214464815497216 : ℝ))/3) ((21-11)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-177667019376837771900037/6140942214464815497216 : ℝ))/36) (((21-11)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-177667019376837771900037/6140942214464815497216 : ℝ))/216) (((21-11)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((30116181184398691347919/13817119982545834868736 : ℝ))/3) ((21-11)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((30116181184398691347919/13817119982545834868736 : ℝ))/36) (((21-11)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((30116181184398691347919/13817119982545834868736 : ℝ))/216) (((21-11)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-11290153506474494427131/124354079842912513818624 : ℝ))/3) ((21-11)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-11290153506474494427131/124354079842912513818624 : ℝ))/36) (((21-11)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-11290153506474494427131/124354079842912513818624 : ℝ))/216) (((21-11)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((18890139867475262663467/8953493748689700994940928 : ℝ))/3) ((21-11)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((18890139867475262663467/8953493748689700994940928 : ℝ))/36) (((21-11)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((18890139867475262663467/8953493748689700994940928 : ℝ))/216) (((21-11)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-578781432778087876871/26860481246069102984822784 : ℝ))/3) ((21-11)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-578781432778087876871/26860481246069102984822784 : ℝ))/36) (((21-11)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-578781432778087876871/26860481246069102984822784 : ℝ))/216) (((21-11)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((70339605743459581/1259085058409489202413568 : ℝ))/3) ((21-11)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((70339605743459581/1259085058409489202413568 : ℝ))/36) (((21-11)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((70339605743459581/1259085058409489202413568 : ℝ))/216) (((21-11)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((100939973621334535/1087849490465798670885322752 : ℝ))/3) ((21-11)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((100939973621334535/1087849490465798670885322752 : ℝ))/36) (((21-11)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((100939973621334535/1087849490465798670885322752 : ℝ))/216) (((21-11)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1470496489030303/6527096942794792025311936512 : ℝ))/3) ((21-11)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1470496489030303/6527096942794792025311936512 : ℝ))/36) (((21-11)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1470496489030303/6527096942794792025311936512 : ℝ))/216) (((21-11)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((70124631227/2175698980931597341770645504 : ℝ))/3) ((21-11)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((70124631227/2175698980931597341770645504 : ℝ))/36) (((21-11)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((70124631227/2175698980931597341770645504 : ℝ))/216) (((21-11)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((24118045/11014476090966211542713892864 : ℝ))/3) ((21-11)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((24118045/11014476090966211542713892864 : ℝ))/36) (((21-11)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((24118045/11014476090966211542713892864 : ℝ))/216) (((21-11)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_11,boundaryZ77]

  ring


def boundaryImCoefficient77_12 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((-1986570578980/531441 : ℝ))/3) ((21-12)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((-1986570578980/531441 : ℝ))/36) (((21-12)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((-1986570578980/531441 : ℝ))/216) (((21-12)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((16747353386672/4782969 : ℝ))/3) ((21-12)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((16747353386672/4782969 : ℝ))/36) (((21-12)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((16747353386672/4782969 : ℝ))/216) (((21-12)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((-2331474115948712719/705277476864 : ℝ))/3) ((21-12)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-2331474115948712719/705277476864 : ℝ))/36) (((21-12)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-2331474115948712719/705277476864 : ℝ))/216) (((21-12)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((6565504311987924541/6347497291776 : ℝ))/3) ((21-12)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((6565504311987924541/6347497291776 : ℝ))/36) (((21-12)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((6565504311987924541/6347497291776 : ℝ))/216) (((21-12)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((-289008052064981183/4760622968832 : ℝ))/3) ((21-12)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-289008052064981183/4760622968832 : ℝ))/36) (((21-12)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-289008052064981183/4760622968832 : ℝ))/216) (((21-12)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-384738771558344262133/10968475320188928 : ℝ))/3) ((21-12)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-384738771558344262133/10968475320188928 : ℝ))/36) (((21-12)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-384738771558344262133/10968475320188928 : ℝ))/216) (((21-12)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((23806395026525945751893/2369190669160808448 : ℝ))/3) ((21-12)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((23806395026525945751893/2369190669160808448 : ℝ))/36) (((21-12)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((23806395026525945751893/2369190669160808448 : ℝ))/216) (((21-12)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((-6416155732178433742061/4738381338321616896 : ℝ))/3) ((21-12)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-6416155732178433742061/4738381338321616896 : ℝ))/36) (((21-12)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-6416155732178433742061/4738381338321616896 : ℝ))/216) (((21-12)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((1797122151745559513509/15992037016835457024 : ℝ))/3) ((21-12)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((1797122151745559513509/15992037016835457024 : ℝ))/36) (((21-12)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((1797122151745559513509/15992037016835457024 : ℝ))/216) (((21-12)+2*8-5)+2) 1 8 A B)))))))) + ((((((boundaryTermCoefficient77 (((-168832731406995898136789/27634239965091669737472 : ℝ))/3) ((21-12)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-168832731406995898136789/27634239965091669737472 : ℝ))/36) (((21-12)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-168832731406995898136789/27634239965091669737472 : ℝ))/216) (((21-12)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((1688705555747040690811/7772129990182032113664 : ℝ))/3) ((21-12)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((1688705555747040690811/7772129990182032113664 : ℝ))/36) (((21-12)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((1688705555747040690811/7772129990182032113664 : ℝ))/216) (((21-12)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((-5438552691705840303863/1119186718586212624367616 : ℝ))/3) ((21-12)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-5438552691705840303863/1119186718586212624367616 : ℝ))/36) (((21-12)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-5438552691705840303863/1119186718586212624367616 : ℝ))/216) (((21-12)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((808998414497480038439/13430240623034551492411392 : ℝ))/3) ((21-12)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((808998414497480038439/13430240623034551492411392 : ℝ))/36) (((21-12)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((808998414497480038439/13430240623034551492411392 : ℝ))/216) (((21-12)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((-6475796502468056641/20145360934551827238617088 : ℝ))/3) ((21-12)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((-6475796502468056641/20145360934551827238617088 : ℝ))/36) (((21-12)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((-6475796502468056641/20145360934551827238617088 : ℝ))/216) (((21-12)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((49987412050768249/90654124205483222573776896 : ℝ))/3) ((21-12)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((49987412050768249/90654124205483222573776896 : ℝ))/36) (((21-12)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((49987412050768249/90654124205483222573776896 : ℝ))/216) (((21-12)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((-5024567107355/33995296577056208465166336 : ℝ))/3) ((21-12)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((-5024567107355/33995296577056208465166336 : ℝ))/36) (((21-12)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((-5024567107355/33995296577056208465166336 : ℝ))/216) (((21-12)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((-118522483457/3263548471397396012655968256 : ℝ))/3) ((21-12)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((-118522483457/3263548471397396012655968256 : ℝ))/36) (((21-12)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((-118522483457/3263548471397396012655968256 : ℝ))/216) (((21-12)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((-991613/917873007580517628559491072 : ℝ))/3) ((21-12)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((-991613/917873007580517628559491072 : ℝ))/36) (((21-12)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((-991613/917873007580517628559491072 : ℝ))/216) (((21-12)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_12_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_12 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_12 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_12

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((-1986570578980/531441 : ℝ))/3) ((21-12)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1986570578980/531441 : ℝ))/36) (((21-12)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1986570578980/531441 : ℝ))/216) (((21-12)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((16747353386672/4782969 : ℝ))/3) ((21-12)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((16747353386672/4782969 : ℝ))/36) (((21-12)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((16747353386672/4782969 : ℝ))/216) (((21-12)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2331474115948712719/705277476864 : ℝ))/3) ((21-12)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2331474115948712719/705277476864 : ℝ))/36) (((21-12)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2331474115948712719/705277476864 : ℝ))/216) (((21-12)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((6565504311987924541/6347497291776 : ℝ))/3) ((21-12)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((6565504311987924541/6347497291776 : ℝ))/36) (((21-12)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((6565504311987924541/6347497291776 : ℝ))/216) (((21-12)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-289008052064981183/4760622968832 : ℝ))/3) ((21-12)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-289008052064981183/4760622968832 : ℝ))/36) (((21-12)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-289008052064981183/4760622968832 : ℝ))/216) (((21-12)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-384738771558344262133/10968475320188928 : ℝ))/3) ((21-12)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-384738771558344262133/10968475320188928 : ℝ))/36) (((21-12)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-384738771558344262133/10968475320188928 : ℝ))/216) (((21-12)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((23806395026525945751893/2369190669160808448 : ℝ))/3) ((21-12)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((23806395026525945751893/2369190669160808448 : ℝ))/36) (((21-12)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((23806395026525945751893/2369190669160808448 : ℝ))/216) (((21-12)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-6416155732178433742061/4738381338321616896 : ℝ))/3) ((21-12)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-6416155732178433742061/4738381338321616896 : ℝ))/36) (((21-12)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-6416155732178433742061/4738381338321616896 : ℝ))/216) (((21-12)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1797122151745559513509/15992037016835457024 : ℝ))/3) ((21-12)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1797122151745559513509/15992037016835457024 : ℝ))/36) (((21-12)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1797122151745559513509/15992037016835457024 : ℝ))/216) (((21-12)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-168832731406995898136789/27634239965091669737472 : ℝ))/3) ((21-12)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-168832731406995898136789/27634239965091669737472 : ℝ))/36) (((21-12)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-168832731406995898136789/27634239965091669737472 : ℝ))/216) (((21-12)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1688705555747040690811/7772129990182032113664 : ℝ))/3) ((21-12)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1688705555747040690811/7772129990182032113664 : ℝ))/36) (((21-12)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1688705555747040690811/7772129990182032113664 : ℝ))/216) (((21-12)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-5438552691705840303863/1119186718586212624367616 : ℝ))/3) ((21-12)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-5438552691705840303863/1119186718586212624367616 : ℝ))/36) (((21-12)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-5438552691705840303863/1119186718586212624367616 : ℝ))/216) (((21-12)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((808998414497480038439/13430240623034551492411392 : ℝ))/3) ((21-12)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((808998414497480038439/13430240623034551492411392 : ℝ))/36) (((21-12)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((808998414497480038439/13430240623034551492411392 : ℝ))/216) (((21-12)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-6475796502468056641/20145360934551827238617088 : ℝ))/3) ((21-12)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-6475796502468056641/20145360934551827238617088 : ℝ))/36) (((21-12)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-6475796502468056641/20145360934551827238617088 : ℝ))/216) (((21-12)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((49987412050768249/90654124205483222573776896 : ℝ))/3) ((21-12)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((49987412050768249/90654124205483222573776896 : ℝ))/36) (((21-12)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((49987412050768249/90654124205483222573776896 : ℝ))/216) (((21-12)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-5024567107355/33995296577056208465166336 : ℝ))/3) ((21-12)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-5024567107355/33995296577056208465166336 : ℝ))/36) (((21-12)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-5024567107355/33995296577056208465166336 : ℝ))/216) (((21-12)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-118522483457/3263548471397396012655968256 : ℝ))/3) ((21-12)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-118522483457/3263548471397396012655968256 : ℝ))/36) (((21-12)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-118522483457/3263548471397396012655968256 : ℝ))/216) (((21-12)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-991613/917873007580517628559491072 : ℝ))/3) ((21-12)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-991613/917873007580517628559491072 : ℝ))/36) (((21-12)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-991613/917873007580517628559491072 : ℝ))/216) (((21-12)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_12,boundaryZ77]

  ring


def boundaryImCoefficient77_13 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((-21387348920/177147 : ℝ))/3) ((21-13)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((-21387348920/177147 : ℝ))/36) (((21-13)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((-21387348920/177147 : ℝ))/216) (((21-13)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((-3394832635850/531441 : ℝ))/3) ((21-13)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((-3394832635850/531441 : ℝ))/36) (((21-13)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((-3394832635850/531441 : ℝ))/216) (((21-13)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((33228267578653235/39182082048 : ℝ))/3) ((21-13)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((33228267578653235/39182082048 : ℝ))/36) (((21-13)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((33228267578653235/39182082048 : ℝ))/216) (((21-13)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((4339944743525504705/3173748645888 : ℝ))/3) ((21-13)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((4339944743525504705/3173748645888 : ℝ))/36) (((21-13)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((4339944743525504705/3173748645888 : ℝ))/216) (((21-13)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((-162875512255664436413/228509902503936 : ℝ))/3) ((21-13)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-162875512255664436413/228509902503936 : ℝ))/36) (((21-13)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-162875512255664436413/228509902503936 : ℝ))/216) (((21-13)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((4431864761983718933/25389989167104 : ℝ))/3) ((21-13)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((4431864761983718933/25389989167104 : ℝ))/36) (((21-13)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((4431864761983718933/25389989167104 : ℝ))/216) (((21-13)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((-31719383994419434377493/1184595334580404224 : ℝ))/3) ((21-13)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((-31719383994419434377493/1184595334580404224 : ℝ))/36) (((21-13)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((-31719383994419434377493/1184595334580404224 : ℝ))/216) (((21-13)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((60167119326862619049737/21322716022447276032 : ℝ))/3) ((21-13)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((60167119326862619049737/21322716022447276032 : ℝ))/36) (((21-13)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((60167119326862619049737/21322716022447276032 : ℝ))/216) (((21-13)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((-53454047900078358757529/255872592269367312384 : ℝ))/3) ((21-13)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-53454047900078358757529/255872592269367312384 : ℝ))/36) (((21-13)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-53454047900078358757529/255872592269367312384 : ℝ))/216) (((21-13)+2*8-5)+2) 1 8 A B)))))))) + ((((((boundaryTermCoefficient77 (((146598159183810982851329/13817119982545834868736 : ℝ))/3) ((21-13)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((146598159183810982851329/13817119982545834868736 : ℝ))/36) (((21-13)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((146598159183810982851329/13817119982545834868736 : ℝ))/216) (((21-13)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((-10918644408274193254457/31088519960728128454656 : ℝ))/3) ((21-13)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((-10918644408274193254457/31088519960728128454656 : ℝ))/36) (((21-13)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((-10918644408274193254457/31088519960728128454656 : ℝ))/216) (((21-13)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((2678650914043232871421/373062239528737541455872 : ℝ))/3) ((21-13)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((2678650914043232871421/373062239528737541455872 : ℝ))/36) (((21-13)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((2678650914043232871421/373062239528737541455872 : ℝ))/216) (((21-13)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((-217482139099894383509/2518170116818978404827136 : ℝ))/3) ((21-13)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-217482139099894383509/2518170116818978404827136 : ℝ))/36) (((21-13)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-217482139099894383509/2518170116818978404827136 : ℝ))/216) (((21-13)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((582702428059627343/1119186718586212624367616 : ℝ))/3) ((21-13)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((582702428059627343/1119186718586212624367616 : ℝ))/36) (((21-13)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((582702428059627343/1119186718586212624367616 : ℝ))/216) (((21-13)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((-2067650774550053/1678780077879318936551424 : ℝ))/3) ((21-13)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((-2067650774550053/1678780077879318936551424 : ℝ))/36) (((21-13)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((-2067650774550053/1678780077879318936551424 : ℝ))/216) (((21-13)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((1533163870865/1888627587614233803620352 : ℝ))/3) ((21-13)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((1533163870865/1888627587614233803620352 : ℝ))/36) (((21-13)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((1533163870865/1888627587614233803620352 : ℝ))/216) (((21-13)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((-59507903/3777255175228467607240704 : ℝ))/3) ((21-13)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((-59507903/3777255175228467607240704 : ℝ))/36) (((21-13)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((-59507903/3777255175228467607240704 : ℝ))/216) (((21-13)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((-2518649/271962372616449667721330688 : ℝ))/3) ((21-13)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((-2518649/271962372616449667721330688 : ℝ))/36) (((21-13)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((-2518649/271962372616449667721330688 : ℝ))/216) (((21-13)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_13_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_13 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_13 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_13

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((-21387348920/177147 : ℝ))/3) ((21-13)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-21387348920/177147 : ℝ))/36) (((21-13)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-21387348920/177147 : ℝ))/216) (((21-13)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-3394832635850/531441 : ℝ))/3) ((21-13)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-3394832635850/531441 : ℝ))/36) (((21-13)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-3394832635850/531441 : ℝ))/216) (((21-13)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((33228267578653235/39182082048 : ℝ))/3) ((21-13)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((33228267578653235/39182082048 : ℝ))/36) (((21-13)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((33228267578653235/39182082048 : ℝ))/216) (((21-13)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((4339944743525504705/3173748645888 : ℝ))/3) ((21-13)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((4339944743525504705/3173748645888 : ℝ))/36) (((21-13)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((4339944743525504705/3173748645888 : ℝ))/216) (((21-13)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-162875512255664436413/228509902503936 : ℝ))/3) ((21-13)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-162875512255664436413/228509902503936 : ℝ))/36) (((21-13)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-162875512255664436413/228509902503936 : ℝ))/216) (((21-13)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((4431864761983718933/25389989167104 : ℝ))/3) ((21-13)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((4431864761983718933/25389989167104 : ℝ))/36) (((21-13)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((4431864761983718933/25389989167104 : ℝ))/216) (((21-13)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-31719383994419434377493/1184595334580404224 : ℝ))/3) ((21-13)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-31719383994419434377493/1184595334580404224 : ℝ))/36) (((21-13)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-31719383994419434377493/1184595334580404224 : ℝ))/216) (((21-13)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((60167119326862619049737/21322716022447276032 : ℝ))/3) ((21-13)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((60167119326862619049737/21322716022447276032 : ℝ))/36) (((21-13)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((60167119326862619049737/21322716022447276032 : ℝ))/216) (((21-13)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-53454047900078358757529/255872592269367312384 : ℝ))/3) ((21-13)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-53454047900078358757529/255872592269367312384 : ℝ))/36) (((21-13)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-53454047900078358757529/255872592269367312384 : ℝ))/216) (((21-13)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((146598159183810982851329/13817119982545834868736 : ℝ))/3) ((21-13)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((146598159183810982851329/13817119982545834868736 : ℝ))/36) (((21-13)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((146598159183810982851329/13817119982545834868736 : ℝ))/216) (((21-13)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-10918644408274193254457/31088519960728128454656 : ℝ))/3) ((21-13)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-10918644408274193254457/31088519960728128454656 : ℝ))/36) (((21-13)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-10918644408274193254457/31088519960728128454656 : ℝ))/216) (((21-13)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((2678650914043232871421/373062239528737541455872 : ℝ))/3) ((21-13)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((2678650914043232871421/373062239528737541455872 : ℝ))/36) (((21-13)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((2678650914043232871421/373062239528737541455872 : ℝ))/216) (((21-13)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-217482139099894383509/2518170116818978404827136 : ℝ))/3) ((21-13)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-217482139099894383509/2518170116818978404827136 : ℝ))/36) (((21-13)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-217482139099894383509/2518170116818978404827136 : ℝ))/216) (((21-13)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((582702428059627343/1119186718586212624367616 : ℝ))/3) ((21-13)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((582702428059627343/1119186718586212624367616 : ℝ))/36) (((21-13)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((582702428059627343/1119186718586212624367616 : ℝ))/216) (((21-13)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2067650774550053/1678780077879318936551424 : ℝ))/3) ((21-13)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2067650774550053/1678780077879318936551424 : ℝ))/36) (((21-13)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2067650774550053/1678780077879318936551424 : ℝ))/216) (((21-13)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1533163870865/1888627587614233803620352 : ℝ))/3) ((21-13)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1533163870865/1888627587614233803620352 : ℝ))/36) (((21-13)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1533163870865/1888627587614233803620352 : ℝ))/216) (((21-13)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-59507903/3777255175228467607240704 : ℝ))/3) ((21-13)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-59507903/3777255175228467607240704 : ℝ))/36) (((21-13)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-59507903/3777255175228467607240704 : ℝ))/216) (((21-13)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2518649/271962372616449667721330688 : ℝ))/3) ((21-13)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2518649/271962372616449667721330688 : ℝ))/36) (((21-13)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2518649/271962372616449667721330688 : ℝ))/216) (((21-13)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_13,boundaryZ77]

  ring


def boundaryImCoefficient77_14 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((-5134963891520/531441 : ℝ))/3) ((21-14)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((-5134963891520/531441 : ℝ))/36) (((21-14)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((-5134963891520/531441 : ℝ))/216) (((21-14)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((-35095739829088/4782969 : ℝ))/3) ((21-14)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((-35095739829088/4782969 : ℝ))/36) (((21-14)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((-35095739829088/4782969 : ℝ))/216) (((21-14)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((604606809589446209/58773123072 : ℝ))/3) ((21-14)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((604606809589446209/58773123072 : ℝ))/36) (((21-14)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((604606809589446209/58773123072 : ℝ))/216) (((21-14)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((-7754220762129884119/1586874322944 : ℝ))/3) ((21-14)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-7754220762129884119/1586874322944 : ℝ))/36) (((21-14)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-7754220762129884119/1586874322944 : ℝ))/216) (((21-14)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((77952780941915794805/57127475625984 : ℝ))/3) ((21-14)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((77952780941915794805/57127475625984 : ℝ))/36) (((21-14)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((77952780941915794805/57127475625984 : ℝ))/216) (((21-14)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-2142573310515031248481/8226356490141696 : ℝ))/3) ((21-14)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-2142573310515031248481/8226356490141696 : ℝ))/36) (((21-14)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-2142573310515031248481/8226356490141696 : ℝ))/216) (((21-14)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((21476636981648276397217/592297667290202112 : ℝ))/3) ((21-14)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((21476636981648276397217/592297667290202112 : ℝ))/36) (((21-14)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((21476636981648276397217/592297667290202112 : ℝ))/216) (((21-14)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((-39705129638856741393889/10661358011223638016 : ℝ))/3) ((21-14)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-39705129638856741393889/10661358011223638016 : ℝ))/36) (((21-14)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-39705129638856741393889/10661358011223638016 : ℝ))/216) (((21-14)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((26276211601461844624817/95952222101012742144 : ℝ))/3) ((21-14)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((26276211601461844624817/95952222101012742144 : ℝ))/36) (((21-14)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((26276211601461844624817/95952222101012742144 : ℝ))/216) (((21-14)+2*8-5)+2) 1 8 A B)))))))) + ((((((boundaryTermCoefficient77 (((-94151306940429308087569/6908559991272917434368 : ℝ))/3) ((21-14)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-94151306940429308087569/6908559991272917434368 : ℝ))/36) (((21-14)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-94151306940429308087569/6908559991272917434368 : ℝ))/216) (((21-14)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((8857539250109601020951/20725679973818752303104 : ℝ))/3) ((21-14)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((8857539250109601020951/20725679973818752303104 : ℝ))/36) (((21-14)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((8857539250109601020951/20725679973818752303104 : ℝ))/216) (((21-14)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((-1099298370620383148009/139898339823276578045952 : ℝ))/3) ((21-14)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-1099298370620383148009/139898339823276578045952 : ℝ))/36) (((21-14)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-1099298370620383148009/139898339823276578045952 : ℝ))/216) (((21-14)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((139479190140860759029/1678780077879318936551424 : ℝ))/3) ((21-14)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((139479190140860759029/1678780077879318936551424 : ℝ))/36) (((21-14)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((139479190140860759029/1678780077879318936551424 : ℝ))/216) (((21-14)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((-90558618457966681/186531119764368770727936 : ℝ))/3) ((21-14)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((-90558618457966681/186531119764368770727936 : ℝ))/36) (((21-14)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((-90558618457966681/186531119764368770727936 : ℝ))/216) (((21-14)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((542692285773281/419695019469829734137856 : ℝ))/3) ((21-14)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((542692285773281/419695019469829734137856 : ℝ))/36) (((21-14)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((542692285773281/419695019469829734137856 : ℝ))/216) (((21-14)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((-2875535311745/2518170116818978404827136 : ℝ))/3) ((21-14)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((-2875535311745/2518170116818978404827136 : ℝ))/36) (((21-14)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((-2875535311745/2518170116818978404827136 : ℝ))/216) (((21-14)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((381175765/2518170116818978404827136 : ℝ))/3) ((21-14)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((381175765/2518170116818978404827136 : ℝ))/36) (((21-14)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((381175765/2518170116818978404827136 : ℝ))/216) (((21-14)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((171157/16997648288528104232583168 : ℝ))/3) ((21-14)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((171157/16997648288528104232583168 : ℝ))/36) (((21-14)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((171157/16997648288528104232583168 : ℝ))/216) (((21-14)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_14_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_14 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_14 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_14

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((-5134963891520/531441 : ℝ))/3) ((21-14)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-5134963891520/531441 : ℝ))/36) (((21-14)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-5134963891520/531441 : ℝ))/216) (((21-14)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-35095739829088/4782969 : ℝ))/3) ((21-14)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-35095739829088/4782969 : ℝ))/36) (((21-14)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-35095739829088/4782969 : ℝ))/216) (((21-14)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((604606809589446209/58773123072 : ℝ))/3) ((21-14)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((604606809589446209/58773123072 : ℝ))/36) (((21-14)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((604606809589446209/58773123072 : ℝ))/216) (((21-14)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-7754220762129884119/1586874322944 : ℝ))/3) ((21-14)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-7754220762129884119/1586874322944 : ℝ))/36) (((21-14)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-7754220762129884119/1586874322944 : ℝ))/216) (((21-14)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((77952780941915794805/57127475625984 : ℝ))/3) ((21-14)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((77952780941915794805/57127475625984 : ℝ))/36) (((21-14)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((77952780941915794805/57127475625984 : ℝ))/216) (((21-14)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2142573310515031248481/8226356490141696 : ℝ))/3) ((21-14)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2142573310515031248481/8226356490141696 : ℝ))/36) (((21-14)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2142573310515031248481/8226356490141696 : ℝ))/216) (((21-14)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((21476636981648276397217/592297667290202112 : ℝ))/3) ((21-14)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((21476636981648276397217/592297667290202112 : ℝ))/36) (((21-14)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((21476636981648276397217/592297667290202112 : ℝ))/216) (((21-14)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-39705129638856741393889/10661358011223638016 : ℝ))/3) ((21-14)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-39705129638856741393889/10661358011223638016 : ℝ))/36) (((21-14)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-39705129638856741393889/10661358011223638016 : ℝ))/216) (((21-14)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((26276211601461844624817/95952222101012742144 : ℝ))/3) ((21-14)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((26276211601461844624817/95952222101012742144 : ℝ))/36) (((21-14)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((26276211601461844624817/95952222101012742144 : ℝ))/216) (((21-14)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-94151306940429308087569/6908559991272917434368 : ℝ))/3) ((21-14)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-94151306940429308087569/6908559991272917434368 : ℝ))/36) (((21-14)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-94151306940429308087569/6908559991272917434368 : ℝ))/216) (((21-14)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((8857539250109601020951/20725679973818752303104 : ℝ))/3) ((21-14)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((8857539250109601020951/20725679973818752303104 : ℝ))/36) (((21-14)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((8857539250109601020951/20725679973818752303104 : ℝ))/216) (((21-14)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1099298370620383148009/139898339823276578045952 : ℝ))/3) ((21-14)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1099298370620383148009/139898339823276578045952 : ℝ))/36) (((21-14)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1099298370620383148009/139898339823276578045952 : ℝ))/216) (((21-14)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((139479190140860759029/1678780077879318936551424 : ℝ))/3) ((21-14)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((139479190140860759029/1678780077879318936551424 : ℝ))/36) (((21-14)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((139479190140860759029/1678780077879318936551424 : ℝ))/216) (((21-14)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-90558618457966681/186531119764368770727936 : ℝ))/3) ((21-14)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-90558618457966681/186531119764368770727936 : ℝ))/36) (((21-14)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-90558618457966681/186531119764368770727936 : ℝ))/216) (((21-14)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((542692285773281/419695019469829734137856 : ℝ))/3) ((21-14)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((542692285773281/419695019469829734137856 : ℝ))/36) (((21-14)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((542692285773281/419695019469829734137856 : ℝ))/216) (((21-14)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2875535311745/2518170116818978404827136 : ℝ))/3) ((21-14)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2875535311745/2518170116818978404827136 : ℝ))/36) (((21-14)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2875535311745/2518170116818978404827136 : ℝ))/216) (((21-14)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((381175765/2518170116818978404827136 : ℝ))/3) ((21-14)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((381175765/2518170116818978404827136 : ℝ))/36) (((21-14)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((381175765/2518170116818978404827136 : ℝ))/216) (((21-14)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((171157/16997648288528104232583168 : ℝ))/3) ((21-14)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((171157/16997648288528104232583168 : ℝ))/36) (((21-14)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((171157/16997648288528104232583168 : ℝ))/216) (((21-14)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_14,boundaryZ77]

  ring


def boundaryImCoefficient77_15 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((-13348111443328/531441 : ℝ))/3) ((21-15)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((-13348111443328/531441 : ℝ))/36) (((21-15)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((-13348111443328/531441 : ℝ))/216) (((21-15)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((121624395483872/4782969 : ℝ))/3) ((21-15)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((121624395483872/4782969 : ℝ))/36) (((21-15)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((121624395483872/4782969 : ℝ))/216) (((21-15)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((-1217373131793371045/88159684608 : ℝ))/3) ((21-15)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-1217373131793371045/88159684608 : ℝ))/36) (((21-15)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-1217373131793371045/88159684608 : ℝ))/216) (((21-15)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((1952289368708571257/396718580736 : ℝ))/3) ((21-15)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((1952289368708571257/396718580736 : ℝ))/36) (((21-15)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((1952289368708571257/396718580736 : ℝ))/216) (((21-15)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((-142384554437803330775/114254951251968 : ℝ))/3) ((21-15)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-142384554437803330775/114254951251968 : ℝ))/36) (((21-15)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-142384554437803330775/114254951251968 : ℝ))/216) (((21-15)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((967959029416596061405/4113178245070848 : ℝ))/3) ((21-15)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((967959029416596061405/4113178245070848 : ℝ))/36) (((21-15)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((967959029416596061405/4113178245070848 : ℝ))/216) (((21-15)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((-9913731652170419685223/296148833645101056 : ℝ))/3) ((21-15)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((-9913731652170419685223/296148833645101056 : ℝ))/36) (((21-15)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((-9913731652170419685223/296148833645101056 : ℝ))/216) (((21-15)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((37298378120628914810429/10661358011223638016 : ℝ))/3) ((21-15)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((37298378120628914810429/10661358011223638016 : ℝ))/36) (((21-15)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((37298378120628914810429/10661358011223638016 : ℝ))/216) (((21-15)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((-49254447986530343382971/191904444202025484288 : ℝ))/3) ((21-15)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-49254447986530343382971/191904444202025484288 : ℝ))/36) (((21-15)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-49254447986530343382971/191904444202025484288 : ℝ))/216) (((21-15)+2*8-5)+2) 1 8 A B)))))))) + ((((((boundaryTermCoefficient77 (((9566163794288972646301/767617776808101937152 : ℝ))/3) ((21-15)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((9566163794288972646301/767617776808101937152 : ℝ))/36) (((21-15)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((9566163794288972646301/767617776808101937152 : ℝ))/216) (((21-15)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((-40034513487506580839/107946249863639334912 : ℝ))/3) ((21-15)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((-40034513487506580839/107946249863639334912 : ℝ))/36) (((21-15)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((-40034513487506580839/107946249863639334912 : ℝ))/216) (((21-15)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((573156975769303689767/93265559882184385363968 : ℝ))/3) ((21-15)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((573156975769303689767/93265559882184385363968 : ℝ))/36) (((21-15)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((573156975769303689767/93265559882184385363968 : ℝ))/216) (((21-15)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((-472692161127254209/8743646238954786127872 : ℝ))/3) ((21-15)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-472692161127254209/8743646238954786127872 : ℝ))/36) (((21-15)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-472692161127254209/8743646238954786127872 : ℝ))/216) (((21-15)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((5624931260846731/20725679973818752303104 : ℝ))/3) ((21-15)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((5624931260846731/20725679973818752303104 : ℝ))/36) (((21-15)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((5624931260846731/20725679973818752303104 : ℝ))/216) (((21-15)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((-213556033693019/279796679646553156091904 : ℝ))/3) ((21-15)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((-213556033693019/279796679646553156091904 : ℝ))/36) (((21-15)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((-213556033693019/279796679646553156091904 : ℝ))/216) (((21-15)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((390571534915/419695019469829734137856 : ℝ))/3) ((21-15)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((390571534915/419695019469829734137856 : ℝ))/36) (((21-15)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((390571534915/419695019469829734137856 : ℝ))/216) (((21-15)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((-839312737/2518170116818978404827136 : ℝ))/3) ((21-15)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((-839312737/2518170116818978404827136 : ℝ))/36) (((21-15)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((-839312737/2518170116818978404827136 : ℝ))/216) (((21-15)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((75943/5665882762842701410861056 : ℝ))/3) ((21-15)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((75943/5665882762842701410861056 : ℝ))/36) (((21-15)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((75943/5665882762842701410861056 : ℝ))/216) (((21-15)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_15_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_15 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_15 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_15

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((-13348111443328/531441 : ℝ))/3) ((21-15)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-13348111443328/531441 : ℝ))/36) (((21-15)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-13348111443328/531441 : ℝ))/216) (((21-15)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((121624395483872/4782969 : ℝ))/3) ((21-15)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((121624395483872/4782969 : ℝ))/36) (((21-15)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((121624395483872/4782969 : ℝ))/216) (((21-15)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1217373131793371045/88159684608 : ℝ))/3) ((21-15)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1217373131793371045/88159684608 : ℝ))/36) (((21-15)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1217373131793371045/88159684608 : ℝ))/216) (((21-15)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1952289368708571257/396718580736 : ℝ))/3) ((21-15)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1952289368708571257/396718580736 : ℝ))/36) (((21-15)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1952289368708571257/396718580736 : ℝ))/216) (((21-15)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-142384554437803330775/114254951251968 : ℝ))/3) ((21-15)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-142384554437803330775/114254951251968 : ℝ))/36) (((21-15)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-142384554437803330775/114254951251968 : ℝ))/216) (((21-15)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((967959029416596061405/4113178245070848 : ℝ))/3) ((21-15)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((967959029416596061405/4113178245070848 : ℝ))/36) (((21-15)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((967959029416596061405/4113178245070848 : ℝ))/216) (((21-15)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-9913731652170419685223/296148833645101056 : ℝ))/3) ((21-15)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-9913731652170419685223/296148833645101056 : ℝ))/36) (((21-15)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-9913731652170419685223/296148833645101056 : ℝ))/216) (((21-15)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((37298378120628914810429/10661358011223638016 : ℝ))/3) ((21-15)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((37298378120628914810429/10661358011223638016 : ℝ))/36) (((21-15)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((37298378120628914810429/10661358011223638016 : ℝ))/216) (((21-15)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-49254447986530343382971/191904444202025484288 : ℝ))/3) ((21-15)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-49254447986530343382971/191904444202025484288 : ℝ))/36) (((21-15)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-49254447986530343382971/191904444202025484288 : ℝ))/216) (((21-15)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((9566163794288972646301/767617776808101937152 : ℝ))/3) ((21-15)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((9566163794288972646301/767617776808101937152 : ℝ))/36) (((21-15)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((9566163794288972646301/767617776808101937152 : ℝ))/216) (((21-15)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-40034513487506580839/107946249863639334912 : ℝ))/3) ((21-15)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-40034513487506580839/107946249863639334912 : ℝ))/36) (((21-15)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-40034513487506580839/107946249863639334912 : ℝ))/216) (((21-15)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((573156975769303689767/93265559882184385363968 : ℝ))/3) ((21-15)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((573156975769303689767/93265559882184385363968 : ℝ))/36) (((21-15)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((573156975769303689767/93265559882184385363968 : ℝ))/216) (((21-15)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-472692161127254209/8743646238954786127872 : ℝ))/3) ((21-15)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-472692161127254209/8743646238954786127872 : ℝ))/36) (((21-15)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-472692161127254209/8743646238954786127872 : ℝ))/216) (((21-15)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((5624931260846731/20725679973818752303104 : ℝ))/3) ((21-15)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((5624931260846731/20725679973818752303104 : ℝ))/36) (((21-15)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((5624931260846731/20725679973818752303104 : ℝ))/216) (((21-15)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-213556033693019/279796679646553156091904 : ℝ))/3) ((21-15)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-213556033693019/279796679646553156091904 : ℝ))/36) (((21-15)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-213556033693019/279796679646553156091904 : ℝ))/216) (((21-15)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((390571534915/419695019469829734137856 : ℝ))/3) ((21-15)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((390571534915/419695019469829734137856 : ℝ))/36) (((21-15)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((390571534915/419695019469829734137856 : ℝ))/216) (((21-15)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-839312737/2518170116818978404827136 : ℝ))/3) ((21-15)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-839312737/2518170116818978404827136 : ℝ))/36) (((21-15)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-839312737/2518170116818978404827136 : ℝ))/216) (((21-15)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((75943/5665882762842701410861056 : ℝ))/3) ((21-15)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((75943/5665882762842701410861056 : ℝ))/36) (((21-15)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((75943/5665882762842701410861056 : ℝ))/216) (((21-15)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_15,boundaryZ77]

  ring


def boundaryImCoefficient77_16 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((2528462995456/531441 : ℝ))/3) ((21-16)+2*0-5) 0 0 A B) + ((boundaryTermCoefficient77 (-((2528462995456/531441 : ℝ))/36) (((21-16)+2*0-5)+1) 1 0 A B) + (boundaryTermCoefficient77 (7*((2528462995456/531441 : ℝ))/216) (((21-16)+2*0-5)+2) 1 0 A B)))) + (((boundaryTermCoefficient77 (((-17099871361024/1594323 : ℝ))/3) ((21-16)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((-17099871361024/1594323 : ℝ))/36) (((21-16)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((-17099871361024/1594323 : ℝ))/216) (((21-16)+2*1-5)+2) 1 1 A B))))) + ((((boundaryTermCoefficient77 (((109574406966704513/14693280768 : ℝ))/3) ((21-16)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((109574406966704513/14693280768 : ℝ))/36) (((21-16)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((109574406966704513/14693280768 : ℝ))/216) (((21-16)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((-375791054218986221/132239526912 : ℝ))/3) ((21-16)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-375791054218986221/132239526912 : ℝ))/36) (((21-16)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-375791054218986221/132239526912 : ℝ))/216) (((21-16)+2*3-5)+2) 1 3 A B)))))) + (((((boundaryTermCoefficient77 (((7018160380710446653/9521245937664 : ℝ))/3) ((21-16)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((7018160380710446653/9521245937664 : ℝ))/36) (((21-16)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((7018160380710446653/9521245937664 : ℝ))/216) (((21-16)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-12218341762226909015/85691213438976 : ℝ))/3) ((21-16)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-12218341762226909015/85691213438976 : ℝ))/36) (((21-16)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-12218341762226909015/85691213438976 : ℝ))/216) (((21-16)+2*5-5)+2) 1 5 A B))))) + ((((boundaryTermCoefficient77 (((170844576349099210283/8226356490141696 : ℝ))/3) ((21-16)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((170844576349099210283/8226356490141696 : ℝ))/36) (((21-16)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((170844576349099210283/8226356490141696 : ℝ))/216) (((21-16)+2*6-5)+2) 1 6 A B)))) + ((((boundaryTermCoefficient77 (((-3909468748870903135145/1776893001870606336 : ℝ))/3) ((21-16)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-3909468748870903135145/1776893001870606336 : ℝ))/36) (((21-16)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-3909468748870903135145/1776893001870606336 : ℝ))/216) (((21-16)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((10312112752460434180081/63968148067341828096 : ℝ))/3) ((21-16)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((10312112752460434180081/63968148067341828096 : ℝ))/36) (((21-16)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((10312112752460434180081/63968148067341828096 : ℝ))/216) (((21-16)+2*8-5)+2) 1 8 A B)))))))) + ((((((boundaryTermCoefficient77 (((-13262401795358356899695/1727139997818229358592 : ℝ))/3) ((21-16)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-13262401795358356899695/1727139997818229358592 : ℝ))/36) (((21-16)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-13262401795358356899695/1727139997818229358592 : ℝ))/216) (((21-16)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((250827967197227695307/1151426665212152905728 : ℝ))/3) ((21-16)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((250827967197227695307/1151426665212152905728 : ℝ))/36) (((21-16)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((250827967197227695307/1151426665212152905728 : ℝ))/216) (((21-16)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((-33197001440833200679/10362839986909376151552 : ℝ))/3) ((21-16)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-33197001440833200679/10362839986909376151552 : ℝ))/36) (((21-16)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-33197001440833200679/10362839986909376151552 : ℝ))/216) (((21-16)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((1901628107210069351/93265559882184385363968 : ℝ))/3) ((21-16)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((1901628107210069351/93265559882184385363968 : ℝ))/36) (((21-16)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((1901628107210069351/93265559882184385363968 : ℝ))/216) (((21-16)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((-576545030764577/10362839986909376151552 : ℝ))/3) ((21-16)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((-576545030764577/10362839986909376151552 : ℝ))/36) (((21-16)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((-576545030764577/10362839986909376151552 : ℝ))/216) (((21-16)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((2362716600431/15544259980364064227328 : ℝ))/3) ((21-16)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((2362716600431/15544259980364064227328 : ℝ))/36) (((21-16)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((2362716600431/15544259980364064227328 : ℝ))/216) (((21-16)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((-58404148283/139898339823276578045952 : ℝ))/3) ((21-16)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((-58404148283/139898339823276578045952 : ℝ))/36) (((21-16)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((-58404148283/139898339823276578045952 : ℝ))/216) (((21-16)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((144740387/419695019469829734137856 : ℝ))/3) ((21-16)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((144740387/419695019469829734137856 : ℝ))/36) (((21-16)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((144740387/419695019469829734137856 : ℝ))/216) (((21-16)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((-4859/157385632301186150301696 : ℝ))/3) ((21-16)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((-4859/157385632301186150301696 : ℝ))/36) (((21-16)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((-4859/157385632301186150301696 : ℝ))/216) (((21-16)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_16_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_16 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_16 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_16

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((2528462995456/531441 : ℝ))/3) ((21-16)+2*0-5) 0 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((2528462995456/531441 : ℝ))/36) (((21-16)+2*0-5)+1) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((2528462995456/531441 : ℝ))/216) (((21-16)+2*0-5)+2) 1 0 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-17099871361024/1594323 : ℝ))/3) ((21-16)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-17099871361024/1594323 : ℝ))/36) (((21-16)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-17099871361024/1594323 : ℝ))/216) (((21-16)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((109574406966704513/14693280768 : ℝ))/3) ((21-16)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((109574406966704513/14693280768 : ℝ))/36) (((21-16)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((109574406966704513/14693280768 : ℝ))/216) (((21-16)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-375791054218986221/132239526912 : ℝ))/3) ((21-16)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-375791054218986221/132239526912 : ℝ))/36) (((21-16)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-375791054218986221/132239526912 : ℝ))/216) (((21-16)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((7018160380710446653/9521245937664 : ℝ))/3) ((21-16)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((7018160380710446653/9521245937664 : ℝ))/36) (((21-16)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((7018160380710446653/9521245937664 : ℝ))/216) (((21-16)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-12218341762226909015/85691213438976 : ℝ))/3) ((21-16)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-12218341762226909015/85691213438976 : ℝ))/36) (((21-16)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-12218341762226909015/85691213438976 : ℝ))/216) (((21-16)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((170844576349099210283/8226356490141696 : ℝ))/3) ((21-16)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((170844576349099210283/8226356490141696 : ℝ))/36) (((21-16)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((170844576349099210283/8226356490141696 : ℝ))/216) (((21-16)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-3909468748870903135145/1776893001870606336 : ℝ))/3) ((21-16)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-3909468748870903135145/1776893001870606336 : ℝ))/36) (((21-16)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-3909468748870903135145/1776893001870606336 : ℝ))/216) (((21-16)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((10312112752460434180081/63968148067341828096 : ℝ))/3) ((21-16)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((10312112752460434180081/63968148067341828096 : ℝ))/36) (((21-16)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((10312112752460434180081/63968148067341828096 : ℝ))/216) (((21-16)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-13262401795358356899695/1727139997818229358592 : ℝ))/3) ((21-16)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-13262401795358356899695/1727139997818229358592 : ℝ))/36) (((21-16)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-13262401795358356899695/1727139997818229358592 : ℝ))/216) (((21-16)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((250827967197227695307/1151426665212152905728 : ℝ))/3) ((21-16)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((250827967197227695307/1151426665212152905728 : ℝ))/36) (((21-16)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((250827967197227695307/1151426665212152905728 : ℝ))/216) (((21-16)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-33197001440833200679/10362839986909376151552 : ℝ))/3) ((21-16)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-33197001440833200679/10362839986909376151552 : ℝ))/36) (((21-16)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-33197001440833200679/10362839986909376151552 : ℝ))/216) (((21-16)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1901628107210069351/93265559882184385363968 : ℝ))/3) ((21-16)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1901628107210069351/93265559882184385363968 : ℝ))/36) (((21-16)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1901628107210069351/93265559882184385363968 : ℝ))/216) (((21-16)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-576545030764577/10362839986909376151552 : ℝ))/3) ((21-16)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-576545030764577/10362839986909376151552 : ℝ))/36) (((21-16)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-576545030764577/10362839986909376151552 : ℝ))/216) (((21-16)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((2362716600431/15544259980364064227328 : ℝ))/3) ((21-16)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((2362716600431/15544259980364064227328 : ℝ))/36) (((21-16)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((2362716600431/15544259980364064227328 : ℝ))/216) (((21-16)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-58404148283/139898339823276578045952 : ℝ))/3) ((21-16)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-58404148283/139898339823276578045952 : ℝ))/36) (((21-16)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-58404148283/139898339823276578045952 : ℝ))/216) (((21-16)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((144740387/419695019469829734137856 : ℝ))/3) ((21-16)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((144740387/419695019469829734137856 : ℝ))/36) (((21-16)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((144740387/419695019469829734137856 : ℝ))/216) (((21-16)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-4859/157385632301186150301696 : ℝ))/3) ((21-16)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-4859/157385632301186150301696 : ℝ))/36) (((21-16)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-4859/157385632301186150301696 : ℝ))/216) (((21-16)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_16,boundaryZ77]

  ring


def boundaryImCoefficient77_17 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((4243318681600/531441 : ℝ))/3) ((21-17)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((4243318681600/531441 : ℝ))/36) (((21-17)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((4243318681600/531441 : ℝ))/216) (((21-17)+2*1-5)+2) 1 1 A B)))) + (((boundaryTermCoefficient77 (((-8177048138099647/2448880128 : ℝ))/3) ((21-17)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-8177048138099647/2448880128 : ℝ))/36) (((21-17)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-8177048138099647/2448880128 : ℝ))/216) (((21-17)+2*2-5)+2) 1 2 A B))))) + ((((boundaryTermCoefficient77 (((9851696752629245/11019960576 : ℝ))/3) ((21-17)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((9851696752629245/11019960576 : ℝ))/36) (((21-17)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((9851696752629245/11019960576 : ℝ))/216) (((21-17)+2*3-5)+2) 1 3 A B)))) + (((boundaryTermCoefficient77 (((-39328210763218429/198359290368 : ℝ))/3) ((21-17)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-39328210763218429/198359290368 : ℝ))/36) (((21-17)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-39328210763218429/198359290368 : ℝ))/216) (((21-17)+2*4-5)+2) 1 4 A B)))))) + (((((boundaryTermCoefficient77 (((2298492282801997615/57127475625984 : ℝ))/3) ((21-17)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((2298492282801997615/57127475625984 : ℝ))/36) (((21-17)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((2298492282801997615/57127475625984 : ℝ))/216) (((21-17)+2*5-5)+2) 1 5 A B)))) + (((boundaryTermCoefficient77 (((-18269417046061876823/2742118830047232 : ℝ))/3) ((21-17)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((-18269417046061876823/2742118830047232 : ℝ))/36) (((21-17)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((-18269417046061876823/2742118830047232 : ℝ))/216) (((21-17)+2*6-5)+2) 1 6 A B))))) + ((((boundaryTermCoefficient77 (((116417121054948576299/148074416822550528 : ℝ))/3) ((21-17)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((116417121054948576299/148074416822550528 : ℝ))/36) (((21-17)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((116417121054948576299/148074416822550528 : ℝ))/216) (((21-17)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((-81442488227202758647/1332669751402954752 : ℝ))/3) ((21-17)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-81442488227202758647/1332669751402954752 : ℝ))/36) (((21-17)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-81442488227202758647/1332669751402954752 : ℝ))/216) (((21-17)+2*8-5)+2) 1 8 A B))))))) + ((((((boundaryTermCoefficient77 (((1686909070369165695149/575713332606076452864 : ℝ))/3) ((21-17)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((1686909070369165695149/575713332606076452864 : ℝ))/36) (((21-17)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((1686909070369165695149/575713332606076452864 : ℝ))/216) (((21-17)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((-14906678686634376827/191904444202025484288 : ℝ))/3) ((21-17)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((-14906678686634376827/191904444202025484288 : ℝ))/36) (((21-17)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((-14906678686634376827/191904444202025484288 : ℝ))/216) (((21-17)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((4434303375353566451/5181419993454688075776 : ℝ))/3) ((21-17)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((4434303375353566451/5181419993454688075776 : ℝ))/36) (((21-17)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((4434303375353566451/5181419993454688075776 : ℝ))/216) (((21-17)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((4125741632104397/3886064995091016056832 : ℝ))/3) ((21-17)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((4125741632104397/3886064995091016056832 : ℝ))/36) (((21-17)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((4125741632104397/3886064995091016056832 : ℝ))/216) (((21-17)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((-105581799586967/1727139997818229358592 : ℝ))/3) ((21-17)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((-105581799586967/1727139997818229358592 : ℝ))/36) (((21-17)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((-105581799586967/1727139997818229358592 : ℝ))/216) (((21-17)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((3445782008879/15544259980364064227328 : ℝ))/3) ((21-17)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((3445782008879/15544259980364064227328 : ℝ))/36) (((21-17)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((3445782008879/15544259980364064227328 : ℝ))/216) (((21-17)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((-6081876911/46632779941092192681984 : ℝ))/3) ((21-17)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((-6081876911/46632779941092192681984 : ℝ))/36) (((21-17)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((-6081876911/46632779941092192681984 : ℝ))/216) (((21-17)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((-1600535/17487292477909572255744 : ℝ))/3) ((21-17)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((-1600535/17487292477909572255744 : ℝ))/36) (((21-17)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((-1600535/17487292477909572255744 : ℝ))/216) (((21-17)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((15397/944313793807116901810176 : ℝ))/3) ((21-17)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((15397/944313793807116901810176 : ℝ))/36) (((21-17)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((15397/944313793807116901810176 : ℝ))/216) (((21-17)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_17_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_17 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_17 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_17

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((4243318681600/531441 : ℝ))/3) ((21-17)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((4243318681600/531441 : ℝ))/36) (((21-17)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((4243318681600/531441 : ℝ))/216) (((21-17)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-8177048138099647/2448880128 : ℝ))/3) ((21-17)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-8177048138099647/2448880128 : ℝ))/36) (((21-17)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-8177048138099647/2448880128 : ℝ))/216) (((21-17)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((9851696752629245/11019960576 : ℝ))/3) ((21-17)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((9851696752629245/11019960576 : ℝ))/36) (((21-17)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((9851696752629245/11019960576 : ℝ))/216) (((21-17)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-39328210763218429/198359290368 : ℝ))/3) ((21-17)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-39328210763218429/198359290368 : ℝ))/36) (((21-17)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-39328210763218429/198359290368 : ℝ))/216) (((21-17)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((2298492282801997615/57127475625984 : ℝ))/3) ((21-17)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((2298492282801997615/57127475625984 : ℝ))/36) (((21-17)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((2298492282801997615/57127475625984 : ℝ))/216) (((21-17)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-18269417046061876823/2742118830047232 : ℝ))/3) ((21-17)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-18269417046061876823/2742118830047232 : ℝ))/36) (((21-17)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-18269417046061876823/2742118830047232 : ℝ))/216) (((21-17)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((116417121054948576299/148074416822550528 : ℝ))/3) ((21-17)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((116417121054948576299/148074416822550528 : ℝ))/36) (((21-17)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((116417121054948576299/148074416822550528 : ℝ))/216) (((21-17)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-81442488227202758647/1332669751402954752 : ℝ))/3) ((21-17)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-81442488227202758647/1332669751402954752 : ℝ))/36) (((21-17)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-81442488227202758647/1332669751402954752 : ℝ))/216) (((21-17)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1686909070369165695149/575713332606076452864 : ℝ))/3) ((21-17)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1686909070369165695149/575713332606076452864 : ℝ))/36) (((21-17)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1686909070369165695149/575713332606076452864 : ℝ))/216) (((21-17)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-14906678686634376827/191904444202025484288 : ℝ))/3) ((21-17)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-14906678686634376827/191904444202025484288 : ℝ))/36) (((21-17)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-14906678686634376827/191904444202025484288 : ℝ))/216) (((21-17)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((4434303375353566451/5181419993454688075776 : ℝ))/3) ((21-17)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((4434303375353566451/5181419993454688075776 : ℝ))/36) (((21-17)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((4434303375353566451/5181419993454688075776 : ℝ))/216) (((21-17)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((4125741632104397/3886064995091016056832 : ℝ))/3) ((21-17)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((4125741632104397/3886064995091016056832 : ℝ))/36) (((21-17)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((4125741632104397/3886064995091016056832 : ℝ))/216) (((21-17)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-105581799586967/1727139997818229358592 : ℝ))/3) ((21-17)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-105581799586967/1727139997818229358592 : ℝ))/36) (((21-17)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-105581799586967/1727139997818229358592 : ℝ))/216) (((21-17)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((3445782008879/15544259980364064227328 : ℝ))/3) ((21-17)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((3445782008879/15544259980364064227328 : ℝ))/36) (((21-17)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((3445782008879/15544259980364064227328 : ℝ))/216) (((21-17)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-6081876911/46632779941092192681984 : ℝ))/3) ((21-17)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-6081876911/46632779941092192681984 : ℝ))/36) (((21-17)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-6081876911/46632779941092192681984 : ℝ))/216) (((21-17)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1600535/17487292477909572255744 : ℝ))/3) ((21-17)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1600535/17487292477909572255744 : ℝ))/36) (((21-17)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1600535/17487292477909572255744 : ℝ))/216) (((21-17)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((15397/944313793807116901810176 : ℝ))/3) ((21-17)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((15397/944313793807116901810176 : ℝ))/36) (((21-17)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((15397/944313793807116901810176 : ℝ))/216) (((21-17)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_17,boundaryZ77]

  ring


def boundaryImCoefficient77_18 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((30183784448/19683 : ℝ))/3) ((21-18)+2*1-5) 0 1 A B) + ((boundaryTermCoefficient77 (-((30183784448/19683 : ℝ))/36) (((21-18)+2*1-5)+1) 1 1 A B) + (boundaryTermCoefficient77 (7*((30183784448/19683 : ℝ))/216) (((21-18)+2*1-5)+2) 1 1 A B)))) + (((boundaryTermCoefficient77 (((-16115551352825/15116544 : ℝ))/3) ((21-18)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-16115551352825/15116544 : ℝ))/36) (((21-18)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-16115551352825/15116544 : ℝ))/216) (((21-18)+2*2-5)+2) 1 2 A B))))) + ((((boundaryTermCoefficient77 (((3054395235517693/7346640384 : ℝ))/3) ((21-18)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((3054395235517693/7346640384 : ℝ))/36) (((21-18)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((3054395235517693/7346640384 : ℝ))/216) (((21-18)+2*3-5)+2) 1 3 A B)))) + (((boundaryTermCoefficient77 (((-75013329306275/816293376 : ℝ))/3) ((21-18)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-75013329306275/816293376 : ℝ))/36) (((21-18)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-75013329306275/816293376 : ℝ))/216) (((21-18)+2*4-5)+2) 1 4 A B)))))) + (((((boundaryTermCoefficient77 (((69537024667402933/6347497291776 : ℝ))/3) ((21-18)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((69537024667402933/6347497291776 : ℝ))/36) (((21-18)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((69537024667402933/6347497291776 : ℝ))/216) (((21-18)+2*5-5)+2) 1 5 A B)))) + (((boundaryTermCoefficient77 (((-641425827648240931/1371059415023616 : ℝ))/3) ((21-18)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((-641425827648240931/1371059415023616 : ℝ))/36) (((21-18)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((-641425827648240931/1371059415023616 : ℝ))/216) (((21-18)+2*6-5)+2) 1 6 A B))))) + ((((boundaryTermCoefficient77 (((-9948386981474227/228509902503936 : ℝ))/3) ((21-18)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-9948386981474227/228509902503936 : ℝ))/36) (((21-18)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-9948386981474227/228509902503936 : ℝ))/216) (((21-18)+2*7-5)+2) 1 7 A B)))) + (((boundaryTermCoefficient77 (((4106602093000574207/592297667290202112 : ℝ))/3) ((21-18)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((4106602093000574207/592297667290202112 : ℝ))/36) (((21-18)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((4106602093000574207/592297667290202112 : ℝ))/216) (((21-18)+2*8-5)+2) 1 8 A B))))))) + ((((((boundaryTermCoefficient77 (((-16652314821037002701/47976111050506371072 : ℝ))/3) ((21-18)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-16652314821037002701/47976111050506371072 : ℝ))/36) (((21-18)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-16652314821037002701/47976111050506371072 : ℝ))/216) (((21-18)+2*9-5)+2) 1 9 A B)))) + (((boundaryTermCoefficient77 (((130424793973229581/31984074033670914048 : ℝ))/3) ((21-18)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((130424793973229581/31984074033670914048 : ℝ))/36) (((21-18)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((130424793973229581/31984074033670914048 : ℝ))/216) (((21-18)+2*10-5)+2) 1 10 A B))))) + ((((boundaryTermCoefficient77 (((51066298187104675/215892499727278669824 : ℝ))/3) ((21-18)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((51066298187104675/215892499727278669824 : ℝ))/36) (((21-18)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((51066298187104675/215892499727278669824 : ℝ))/216) (((21-18)+2*11-5)+2) 1 11 A B)))) + (((boundaryTermCoefficient77 (((-21107016783832027/2590709996727344037888 : ℝ))/3) ((21-18)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-21107016783832027/2590709996727344037888 : ℝ))/36) (((21-18)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-21107016783832027/2590709996727344037888 : ℝ))/216) (((21-18)+2*12-5)+2) 1 12 A B)))))) + (((((boundaryTermCoefficient77 (((24039534658013/287856666303038226432 : ℝ))/3) ((21-18)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((24039534658013/287856666303038226432 : ℝ))/36) (((21-18)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((24039534658013/287856666303038226432 : ℝ))/216) (((21-18)+2*13-5)+2) 1 13 A B)))) + (((boundaryTermCoefficient77 (((-203854763177/647677499181836009472 : ℝ))/3) ((21-18)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((-203854763177/647677499181836009472 : ℝ))/36) (((21-18)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((-203854763177/647677499181836009472 : ℝ))/216) (((21-18)+2*14-5)+2) 1 14 A B))))) + ((((boundaryTermCoefficient77 (((3249860191/7772129990182032113664 : ℝ))/3) ((21-18)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((3249860191/7772129990182032113664 : ℝ))/36) (((21-18)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((3249860191/7772129990182032113664 : ℝ))/216) (((21-18)+2*15-5)+2) 1 15 A B)))) + ((((boundaryTermCoefficient77 (((-1323349/8743646238954786127872 : ℝ))/3) ((21-18)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((-1323349/8743646238954786127872 : ℝ))/36) (((21-18)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((-1323349/8743646238954786127872 : ℝ))/216) (((21-18)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((245/39346408075296537575424 : ℝ))/3) ((21-18)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((245/39346408075296537575424 : ℝ))/36) (((21-18)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((245/39346408075296537575424 : ℝ))/216) (((21-18)+2*17-5)+2) 1 17 A B)))))))))

theorem boundaryImCoefficient77_18_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_18 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_18 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_18

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((30183784448/19683 : ℝ))/3) ((21-18)+2*1-5) 0 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((30183784448/19683 : ℝ))/36) (((21-18)+2*1-5)+1) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((30183784448/19683 : ℝ))/216) (((21-18)+2*1-5)+2) 1 1 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-16115551352825/15116544 : ℝ))/3) ((21-18)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-16115551352825/15116544 : ℝ))/36) (((21-18)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-16115551352825/15116544 : ℝ))/216) (((21-18)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((3054395235517693/7346640384 : ℝ))/3) ((21-18)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((3054395235517693/7346640384 : ℝ))/36) (((21-18)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((3054395235517693/7346640384 : ℝ))/216) (((21-18)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-75013329306275/816293376 : ℝ))/3) ((21-18)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-75013329306275/816293376 : ℝ))/36) (((21-18)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-75013329306275/816293376 : ℝ))/216) (((21-18)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((69537024667402933/6347497291776 : ℝ))/3) ((21-18)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((69537024667402933/6347497291776 : ℝ))/36) (((21-18)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((69537024667402933/6347497291776 : ℝ))/216) (((21-18)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-641425827648240931/1371059415023616 : ℝ))/3) ((21-18)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-641425827648240931/1371059415023616 : ℝ))/36) (((21-18)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-641425827648240931/1371059415023616 : ℝ))/216) (((21-18)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-9948386981474227/228509902503936 : ℝ))/3) ((21-18)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-9948386981474227/228509902503936 : ℝ))/36) (((21-18)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-9948386981474227/228509902503936 : ℝ))/216) (((21-18)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((4106602093000574207/592297667290202112 : ℝ))/3) ((21-18)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((4106602093000574207/592297667290202112 : ℝ))/36) (((21-18)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((4106602093000574207/592297667290202112 : ℝ))/216) (((21-18)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-16652314821037002701/47976111050506371072 : ℝ))/3) ((21-18)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-16652314821037002701/47976111050506371072 : ℝ))/36) (((21-18)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-16652314821037002701/47976111050506371072 : ℝ))/216) (((21-18)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((130424793973229581/31984074033670914048 : ℝ))/3) ((21-18)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((130424793973229581/31984074033670914048 : ℝ))/36) (((21-18)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((130424793973229581/31984074033670914048 : ℝ))/216) (((21-18)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((51066298187104675/215892499727278669824 : ℝ))/3) ((21-18)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((51066298187104675/215892499727278669824 : ℝ))/36) (((21-18)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((51066298187104675/215892499727278669824 : ℝ))/216) (((21-18)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-21107016783832027/2590709996727344037888 : ℝ))/3) ((21-18)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-21107016783832027/2590709996727344037888 : ℝ))/36) (((21-18)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-21107016783832027/2590709996727344037888 : ℝ))/216) (((21-18)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((24039534658013/287856666303038226432 : ℝ))/3) ((21-18)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((24039534658013/287856666303038226432 : ℝ))/36) (((21-18)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((24039534658013/287856666303038226432 : ℝ))/216) (((21-18)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-203854763177/647677499181836009472 : ℝ))/3) ((21-18)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-203854763177/647677499181836009472 : ℝ))/36) (((21-18)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-203854763177/647677499181836009472 : ℝ))/216) (((21-18)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((3249860191/7772129990182032113664 : ℝ))/3) ((21-18)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((3249860191/7772129990182032113664 : ℝ))/36) (((21-18)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((3249860191/7772129990182032113664 : ℝ))/216) (((21-18)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1323349/8743646238954786127872 : ℝ))/3) ((21-18)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1323349/8743646238954786127872 : ℝ))/36) (((21-18)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1323349/8743646238954786127872 : ℝ))/216) (((21-18)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((245/39346408075296537575424 : ℝ))/3) ((21-18)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((245/39346408075296537575424 : ℝ))/36) (((21-18)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((245/39346408075296537575424 : ℝ))/216) (((21-18)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_18,boundaryZ77]

  ring


def boundaryImCoefficient77_19 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((29795377108907/34012224 : ℝ))/3) ((21-19)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((29795377108907/34012224 : ℝ))/36) (((21-19)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((29795377108907/34012224 : ℝ))/216) (((21-19)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((-437897528894045/1224440064 : ℝ))/3) ((21-19)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-437897528894045/1224440064 : ℝ))/36) (((21-19)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-437897528894045/1224440064 : ℝ))/216) (((21-19)+2*3-5)+2) 1 3 A B))))) + ((((boundaryTermCoefficient77 (((15644466017518031/176319369216 : ℝ))/3) ((21-19)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((15644466017518031/176319369216 : ℝ))/36) (((21-19)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((15644466017518031/176319369216 : ℝ))/216) (((21-19)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-90981090116776051/6347497291776 : ℝ))/3) ((21-19)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-90981090116776051/6347497291776 : ℝ))/36) (((21-19)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-90981090116776051/6347497291776 : ℝ))/216) (((21-19)+2*5-5)+2) 1 5 A B)))))) + (((((boundaryTermCoefficient77 (((120098757160894523/76169967501312 : ℝ))/3) ((21-19)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((120098757160894523/76169967501312 : ℝ))/36) (((21-19)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((120098757160894523/76169967501312 : ℝ))/216) (((21-19)+2*6-5)+2) 1 6 A B)))) + (((boundaryTermCoefficient77 (((-507242181469983599/4113178245070848 : ℝ))/3) ((21-19)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-507242181469983599/4113178245070848 : ℝ))/36) (((21-19)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-507242181469983599/4113178245070848 : ℝ))/216) (((21-19)+2*7-5)+2) 1 7 A B))))) + ((((boundaryTermCoefficient77 (((2156268021145190891/296148833645101056 : ℝ))/3) ((21-19)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((2156268021145190891/296148833645101056 : ℝ))/36) (((21-19)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((2156268021145190891/296148833645101056 : ℝ))/216) (((21-19)+2*8-5)+2) 1 8 A B)))) + (((boundaryTermCoefficient77 (((-693695452583458339/1999004627104432128 : ℝ))/3) ((21-19)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-693695452583458339/1999004627104432128 : ℝ))/36) (((21-19)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-693695452583458339/1999004627104432128 : ℝ))/216) (((21-19)+2*9-5)+2) 1 9 A B))))))) + ((((((boundaryTermCoefficient77 (((1115739130466579/83291859462684672 : ℝ))/3) ((21-19)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((1115739130466579/83291859462684672 : ℝ))/36) (((21-19)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((1115739130466579/83291859462684672 : ℝ))/216) (((21-19)+2*10-5)+2) 1 10 A B)))) + (((boundaryTermCoefficient77 (((-17933669805700133/47976111050506371072 : ℝ))/3) ((21-19)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-17933669805700133/47976111050506371072 : ℝ))/36) (((21-19)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-17933669805700133/47976111050506371072 : ℝ))/216) (((21-19)+2*11-5)+2) 1 11 A B))))) + ((((boundaryTermCoefficient77 (((2719178938354451/431784999454557339648 : ℝ))/3) ((21-19)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((2719178938354451/431784999454557339648 : ℝ))/36) (((21-19)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((2719178938354451/431784999454557339648 : ℝ))/216) (((21-19)+2*12-5)+2) 1 12 A B)))) + (((boundaryTermCoefficient77 (((-1297901232197/23988055525253185536 : ℝ))/3) ((21-19)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((-1297901232197/23988055525253185536 : ℝ))/36) (((21-19)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((-1297901232197/23988055525253185536 : ℝ))/216) (((21-19)+2*13-5)+2) 1 13 A B)))))) + (((((boundaryTermCoefficient77 (((15237188201/71964166575759556608 : ℝ))/3) ((21-19)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((15237188201/71964166575759556608 : ℝ))/36) (((21-19)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((15237188201/71964166575759556608 : ℝ))/216) (((21-19)+2*14-5)+2) 1 14 A B)))) + (((boundaryTermCoefficient77 (((-1299579569/3886064995091016056832 : ℝ))/3) ((21-19)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((-1299579569/3886064995091016056832 : ℝ))/36) (((21-19)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((-1299579569/3886064995091016056832 : ℝ))/216) (((21-19)+2*15-5)+2) 1 15 A B))))) + ((((boundaryTermCoefficient77 (((638777/3886064995091016056832 : ℝ))/3) ((21-19)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((638777/3886064995091016056832 : ℝ))/36) (((21-19)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((638777/3886064995091016056832 : ℝ))/216) (((21-19)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((-47/4371823119477393063936 : ℝ))/3) ((21-19)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((-47/4371823119477393063936 : ℝ))/36) (((21-19)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((-47/4371823119477393063936 : ℝ))/216) (((21-19)+2*17-5)+2) 1 17 A B))))))))

theorem boundaryImCoefficient77_19_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_19 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_19 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_19

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((29795377108907/34012224 : ℝ))/3) ((21-19)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((29795377108907/34012224 : ℝ))/36) (((21-19)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((29795377108907/34012224 : ℝ))/216) (((21-19)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-437897528894045/1224440064 : ℝ))/3) ((21-19)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-437897528894045/1224440064 : ℝ))/36) (((21-19)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-437897528894045/1224440064 : ℝ))/216) (((21-19)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((15644466017518031/176319369216 : ℝ))/3) ((21-19)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((15644466017518031/176319369216 : ℝ))/36) (((21-19)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((15644466017518031/176319369216 : ℝ))/216) (((21-19)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-90981090116776051/6347497291776 : ℝ))/3) ((21-19)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-90981090116776051/6347497291776 : ℝ))/36) (((21-19)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-90981090116776051/6347497291776 : ℝ))/216) (((21-19)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((120098757160894523/76169967501312 : ℝ))/3) ((21-19)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((120098757160894523/76169967501312 : ℝ))/36) (((21-19)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((120098757160894523/76169967501312 : ℝ))/216) (((21-19)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-507242181469983599/4113178245070848 : ℝ))/3) ((21-19)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-507242181469983599/4113178245070848 : ℝ))/36) (((21-19)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-507242181469983599/4113178245070848 : ℝ))/216) (((21-19)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((2156268021145190891/296148833645101056 : ℝ))/3) ((21-19)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((2156268021145190891/296148833645101056 : ℝ))/36) (((21-19)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((2156268021145190891/296148833645101056 : ℝ))/216) (((21-19)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-693695452583458339/1999004627104432128 : ℝ))/3) ((21-19)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-693695452583458339/1999004627104432128 : ℝ))/36) (((21-19)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-693695452583458339/1999004627104432128 : ℝ))/216) (((21-19)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1115739130466579/83291859462684672 : ℝ))/3) ((21-19)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1115739130466579/83291859462684672 : ℝ))/36) (((21-19)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1115739130466579/83291859462684672 : ℝ))/216) (((21-19)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-17933669805700133/47976111050506371072 : ℝ))/3) ((21-19)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-17933669805700133/47976111050506371072 : ℝ))/36) (((21-19)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-17933669805700133/47976111050506371072 : ℝ))/216) (((21-19)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((2719178938354451/431784999454557339648 : ℝ))/3) ((21-19)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((2719178938354451/431784999454557339648 : ℝ))/36) (((21-19)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((2719178938354451/431784999454557339648 : ℝ))/216) (((21-19)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1297901232197/23988055525253185536 : ℝ))/3) ((21-19)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1297901232197/23988055525253185536 : ℝ))/36) (((21-19)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1297901232197/23988055525253185536 : ℝ))/216) (((21-19)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((15237188201/71964166575759556608 : ℝ))/3) ((21-19)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((15237188201/71964166575759556608 : ℝ))/36) (((21-19)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((15237188201/71964166575759556608 : ℝ))/216) (((21-19)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1299579569/3886064995091016056832 : ℝ))/3) ((21-19)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1299579569/3886064995091016056832 : ℝ))/36) (((21-19)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1299579569/3886064995091016056832 : ℝ))/216) (((21-19)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((638777/3886064995091016056832 : ℝ))/3) ((21-19)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((638777/3886064995091016056832 : ℝ))/36) (((21-19)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((638777/3886064995091016056832 : ℝ))/216) (((21-19)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-47/4371823119477393063936 : ℝ))/3) ((21-19)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-47/4371823119477393063936 : ℝ))/36) (((21-19)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-47/4371823119477393063936 : ℝ))/216) (((21-19)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_19,boundaryZ77]

  ring


def boundaryImCoefficient77_20 (A B : ℕ) : ℝ :=
  (((((((boundaryTermCoefficient77 (((-82847596544/177147 : ℝ))/3) ((21-20)+2*2-5) 0 2 A B) + ((boundaryTermCoefficient77 (-((-82847596544/177147 : ℝ))/36) (((21-20)+2*2-5)+1) 1 2 A B) + (boundaryTermCoefficient77 (7*((-82847596544/177147 : ℝ))/216) (((21-20)+2*2-5)+2) 1 2 A B)))) + (((boundaryTermCoefficient77 (((4398482249537/25509168 : ℝ))/3) ((21-20)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((4398482249537/25509168 : ℝ))/36) (((21-20)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((4398482249537/25509168 : ℝ))/216) (((21-20)+2*3-5)+2) 1 3 A B))))) + ((((boundaryTermCoefficient77 (((-76317551083573/1836660096 : ℝ))/3) ((21-20)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((-76317551083573/1836660096 : ℝ))/36) (((21-20)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((-76317551083573/1836660096 : ℝ))/216) (((21-20)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((114351004022381/16529940864 : ℝ))/3) ((21-20)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((114351004022381/16529940864 : ℝ))/36) (((21-20)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((114351004022381/16529940864 : ℝ))/216) (((21-20)+2*5-5)+2) 1 5 A B)))))) + (((((boundaryTermCoefficient77 (((-1304943382921777/1586874322944 : ℝ))/3) ((21-20)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((-1304943382921777/1586874322944 : ℝ))/36) (((21-20)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((-1304943382921777/1586874322944 : ℝ))/216) (((21-20)+2*6-5)+2) 1 6 A B)))) + (((boundaryTermCoefficient77 (((12206930250593419/171382426877952 : ℝ))/3) ((21-20)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((12206930250593419/171382426877952 : ℝ))/36) (((21-20)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((12206930250593419/171382426877952 : ℝ))/216) (((21-20)+2*7-5)+2) 1 7 A B))))) + ((((boundaryTermCoefficient77 (((-7004604422418047/1542441841901568 : ℝ))/3) ((21-20)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((-7004604422418047/1542441841901568 : ℝ))/36) (((21-20)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((-7004604422418047/1542441841901568 : ℝ))/216) (((21-20)+2*8-5)+2) 1 8 A B)))) + (((boundaryTermCoefficient77 (((141722042087919145/666334875701477376 : ℝ))/3) ((21-20)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((141722042087919145/666334875701477376 : ℝ))/36) (((21-20)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((141722042087919145/666334875701477376 : ℝ))/216) (((21-20)+2*9-5)+2) 1 9 A B))))))) + ((((((boundaryTermCoefficient77 (((-3182611997616607/444223250467651584 : ℝ))/3) ((21-20)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((-3182611997616607/444223250467651584 : ℝ))/36) (((21-20)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((-3182611997616607/444223250467651584 : ℝ))/216) (((21-20)+2*10-5)+2) 1 10 A B)))) + (((boundaryTermCoefficient77 (((1980514142210113/11994027762626592768 : ℝ))/3) ((21-20)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((1980514142210113/11994027762626592768 : ℝ))/36) (((21-20)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((1980514142210113/11994027762626592768 : ℝ))/216) (((21-20)+2*11-5)+2) 1 11 A B))))) + ((((boundaryTermCoefficient77 (((-171678661461703/71964166575759556608 : ℝ))/3) ((21-20)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((-171678661461703/71964166575759556608 : ℝ))/36) (((21-20)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((-171678661461703/71964166575759556608 : ℝ))/216) (((21-20)+2*12-5)+2) 1 12 A B)))) + (((boundaryTermCoefficient77 (((12789770267/666334875701477376 : ℝ))/3) ((21-20)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((12789770267/666334875701477376 : ℝ))/36) (((21-20)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((12789770267/666334875701477376 : ℝ))/216) (((21-20)+2*13-5)+2) 1 13 A B)))))) + (((((boundaryTermCoefficient77 (((-2047532911/26986562465909833728 : ℝ))/3) ((21-20)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((-2047532911/26986562465909833728 : ℝ))/36) (((21-20)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((-2047532911/26986562465909833728 : ℝ))/216) (((21-20)+2*14-5)+2) 1 14 A B)))) + (((boundaryTermCoefficient77 (((40807745/323838749590918004736 : ℝ))/3) ((21-20)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((40807745/323838749590918004736 : ℝ))/36) (((21-20)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((40807745/323838749590918004736 : ℝ))/216) (((21-20)+2*15-5)+2) 1 15 A B))))) + ((((boundaryTermCoefficient77 (((-4747/71964166575759556608 : ℝ))/3) ((21-20)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((-4747/71964166575759556608 : ℝ))/36) (((21-20)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((-4747/71964166575759556608 : ℝ))/216) (((21-20)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((5/1092955779869348265984 : ℝ))/3) ((21-20)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((5/1092955779869348265984 : ℝ))/36) (((21-20)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((5/1092955779869348265984 : ℝ))/216) (((21-20)+2*17-5)+2) 1 17 A B))))))))

theorem boundaryImCoefficient77_20_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_20 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_20 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_20

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((-82847596544/177147 : ℝ))/3) ((21-20)+2*2-5) 0 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-82847596544/177147 : ℝ))/36) (((21-20)+2*2-5)+1) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-82847596544/177147 : ℝ))/216) (((21-20)+2*2-5)+2) 1 2 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((4398482249537/25509168 : ℝ))/3) ((21-20)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((4398482249537/25509168 : ℝ))/36) (((21-20)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((4398482249537/25509168 : ℝ))/216) (((21-20)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-76317551083573/1836660096 : ℝ))/3) ((21-20)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-76317551083573/1836660096 : ℝ))/36) (((21-20)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-76317551083573/1836660096 : ℝ))/216) (((21-20)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((114351004022381/16529940864 : ℝ))/3) ((21-20)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((114351004022381/16529940864 : ℝ))/36) (((21-20)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((114351004022381/16529940864 : ℝ))/216) (((21-20)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1304943382921777/1586874322944 : ℝ))/3) ((21-20)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1304943382921777/1586874322944 : ℝ))/36) (((21-20)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1304943382921777/1586874322944 : ℝ))/216) (((21-20)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((12206930250593419/171382426877952 : ℝ))/3) ((21-20)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((12206930250593419/171382426877952 : ℝ))/36) (((21-20)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((12206930250593419/171382426877952 : ℝ))/216) (((21-20)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-7004604422418047/1542441841901568 : ℝ))/3) ((21-20)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-7004604422418047/1542441841901568 : ℝ))/36) (((21-20)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-7004604422418047/1542441841901568 : ℝ))/216) (((21-20)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((141722042087919145/666334875701477376 : ℝ))/3) ((21-20)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((141722042087919145/666334875701477376 : ℝ))/36) (((21-20)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((141722042087919145/666334875701477376 : ℝ))/216) (((21-20)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-3182611997616607/444223250467651584 : ℝ))/3) ((21-20)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-3182611997616607/444223250467651584 : ℝ))/36) (((21-20)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-3182611997616607/444223250467651584 : ℝ))/216) (((21-20)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((1980514142210113/11994027762626592768 : ℝ))/3) ((21-20)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((1980514142210113/11994027762626592768 : ℝ))/36) (((21-20)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((1980514142210113/11994027762626592768 : ℝ))/216) (((21-20)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-171678661461703/71964166575759556608 : ℝ))/3) ((21-20)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-171678661461703/71964166575759556608 : ℝ))/36) (((21-20)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-171678661461703/71964166575759556608 : ℝ))/216) (((21-20)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((12789770267/666334875701477376 : ℝ))/3) ((21-20)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((12789770267/666334875701477376 : ℝ))/36) (((21-20)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((12789770267/666334875701477376 : ℝ))/216) (((21-20)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2047532911/26986562465909833728 : ℝ))/3) ((21-20)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2047532911/26986562465909833728 : ℝ))/36) (((21-20)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2047532911/26986562465909833728 : ℝ))/216) (((21-20)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((40807745/323838749590918004736 : ℝ))/3) ((21-20)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((40807745/323838749590918004736 : ℝ))/36) (((21-20)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((40807745/323838749590918004736 : ℝ))/216) (((21-20)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-4747/71964166575759556608 : ℝ))/3) ((21-20)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-4747/71964166575759556608 : ℝ))/36) (((21-20)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-4747/71964166575759556608 : ℝ))/216) (((21-20)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((5/1092955779869348265984 : ℝ))/3) ((21-20)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((5/1092955779869348265984 : ℝ))/36) (((21-20)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((5/1092955779869348265984 : ℝ))/216) (((21-20)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_20,boundaryZ77]

  ring


def boundaryImCoefficient77_21 (A B : ℕ) : ℝ :=
  ((((((boundaryTermCoefficient77 (((-2116157440/59049 : ℝ))/3) ((21-21)+2*3-5) 0 3 A B) + ((boundaryTermCoefficient77 (-((-2116157440/59049 : ℝ))/36) (((21-21)+2*3-5)+1) 1 3 A B) + (boundaryTermCoefficient77 (7*((-2116157440/59049 : ℝ))/216) (((21-21)+2*3-5)+2) 1 3 A B)))) + ((((boundaryTermCoefficient77 (((40487047168/4782969 : ℝ))/3) ((21-21)+2*4-5) 0 4 A B) + ((boundaryTermCoefficient77 (-((40487047168/4782969 : ℝ))/36) (((21-21)+2*4-5)+1) 1 4 A B) + (boundaryTermCoefficient77 (7*((40487047168/4782969 : ℝ))/216) (((21-21)+2*4-5)+2) 1 4 A B)))) + (((boundaryTermCoefficient77 (((-60155799296/43046721 : ℝ))/3) ((21-21)+2*5-5) 0 5 A B) + ((boundaryTermCoefficient77 (-((-60155799296/43046721 : ℝ))/36) (((21-21)+2*5-5)+1) 1 5 A B) + (boundaryTermCoefficient77 (7*((-60155799296/43046721 : ℝ))/216) (((21-21)+2*5-5)+2) 1 5 A B)))))) + (((((boundaryTermCoefficient77 (((16458456017087/99179645184 : ℝ))/3) ((21-21)+2*6-5) 0 6 A B) + ((boundaryTermCoefficient77 (-((16458456017087/99179645184 : ℝ))/36) (((21-21)+2*6-5)+1) 1 6 A B) + (boundaryTermCoefficient77 (7*((16458456017087/99179645184 : ℝ))/216) (((21-21)+2*6-5)+2) 1 6 A B)))) + (((boundaryTermCoefficient77 (((-3202435542593/223154201664 : ℝ))/3) ((21-21)+2*7-5) 0 7 A B) + ((boundaryTermCoefficient77 (-((-3202435542593/223154201664 : ℝ))/36) (((21-21)+2*7-5)+1) 1 7 A B) + (boundaryTermCoefficient77 (7*((-3202435542593/223154201664 : ℝ))/216) (((21-21)+2*7-5)+2) 1 7 A B))))) + ((((boundaryTermCoefficient77 (((464622800108815/514147280633856 : ℝ))/3) ((21-21)+2*8-5) 0 8 A B) + ((boundaryTermCoefficient77 (-((464622800108815/514147280633856 : ℝ))/36) (((21-21)+2*8-5)+1) 1 8 A B) + (boundaryTermCoefficient77 (7*((464622800108815/514147280633856 : ℝ))/216) (((21-21)+2*8-5)+2) 1 8 A B)))) + (((boundaryTermCoefficient77 (((-2273787291250585/55527906308456448 : ℝ))/3) ((21-21)+2*9-5) 0 9 A B) + ((boundaryTermCoefficient77 (-((-2273787291250585/55527906308456448 : ℝ))/36) (((21-21)+2*9-5)+1) 1 9 A B) + (boundaryTermCoefficient77 (7*((-2273787291250585/55527906308456448 : ℝ))/216) (((21-21)+2*9-5)+2) 1 9 A B))))))) + ((((((boundaryTermCoefficient77 (((96411338058443/74037208411275264 : ℝ))/3) ((21-21)+2*10-5) 0 10 A B) + ((boundaryTermCoefficient77 (-((96411338058443/74037208411275264 : ℝ))/36) (((21-21)+2*10-5)+1) 1 10 A B) + (boundaryTermCoefficient77 (7*((96411338058443/74037208411275264 : ℝ))/216) (((21-21)+2*10-5)+2) 1 10 A B)))) + (((boundaryTermCoefficient77 (((-27853481344505/999502313552216064 : ℝ))/3) ((21-21)+2*11-5) 0 11 A B) + ((boundaryTermCoefficient77 (-((-27853481344505/999502313552216064 : ℝ))/36) (((21-21)+2*11-5)+1) 1 11 A B) + (boundaryTermCoefficient77 (7*((-27853481344505/999502313552216064 : ℝ))/216) (((21-21)+2*11-5)+2) 1 11 A B))))) + ((((boundaryTermCoefficient77 (((140944386775/374813367582081024 : ℝ))/3) ((21-21)+2*12-5) 0 12 A B) + ((boundaryTermCoefficient77 (-((140944386775/374813367582081024 : ℝ))/36) (((21-21)+2*12-5)+1) 1 12 A B) + (boundaryTermCoefficient77 (7*((140944386775/374813367582081024 : ℝ))/216) (((21-21)+2*12-5)+2) 1 12 A B)))) + (((boundaryTermCoefficient77 (((-5818211165/1999004627104432128 : ℝ))/3) ((21-21)+2*13-5) 0 13 A B) + ((boundaryTermCoefficient77 (-((-5818211165/1999004627104432128 : ℝ))/36) (((21-21)+2*13-5)+1) 1 13 A B) + (boundaryTermCoefficient77 (7*((-5818211165/1999004627104432128 : ℝ))/216) (((21-21)+2*13-5)+2) 1 13 A B)))))) + (((((boundaryTermCoefficient77 (((204815881/17991041643939889152 : ℝ))/3) ((21-21)+2*14-5) 0 14 A B) + ((boundaryTermCoefficient77 (-((204815881/17991041643939889152 : ℝ))/36) (((21-21)+2*14-5)+1) 1 14 A B) + (boundaryTermCoefficient77 (7*((204815881/17991041643939889152 : ℝ))/216) (((21-21)+2*14-5)+2) 1 14 A B)))) + (((boundaryTermCoefficient77 (((-255391/13493281232954916864 : ℝ))/3) ((21-21)+2*15-5) 0 15 A B) + ((boundaryTermCoefficient77 (-((-255391/13493281232954916864 : ℝ))/36) (((21-21)+2*15-5)+1) 1 15 A B) + (boundaryTermCoefficient77 (7*((-255391/13493281232954916864 : ℝ))/216) (((21-21)+2*15-5)+2) 1 15 A B))))) + ((((boundaryTermCoefficient77 (((803/80959687397729501184 : ℝ))/3) ((21-21)+2*16-5) 0 16 A B) + ((boundaryTermCoefficient77 (-((803/80959687397729501184 : ℝ))/36) (((21-21)+2*16-5)+1) 1 16 A B) + (boundaryTermCoefficient77 (7*((803/80959687397729501184 : ℝ))/216) (((21-21)+2*16-5)+2) 1 16 A B)))) + (((boundaryTermCoefficient77 (((-1/1457274373159131021312 : ℝ))/3) ((21-21)+2*17-5) 0 17 A B) + ((boundaryTermCoefficient77 (-((-1/1457274373159131021312 : ℝ))/36) (((21-21)+2*17-5)+1) 1 17 A B) + (boundaryTermCoefficient77 (7*((-1/1457274373159131021312 : ℝ))/216) (((21-21)+2*17-5)+2) 1 17 A B))))))))

theorem boundaryImCoefficient77_21_reconstruction (t v : ℝ) :

    boundaryBernstein77 boundaryImCoefficient77_21 t v=boundaryZ77 (boundaryH77*t) (boundaryS77*v)*boundaryImHighColumn77_21 (boundaryH77*t) (boundaryR77 (boundaryH77*t) (boundaryS77*v)) := by

  unfold boundaryImCoefficient77_21

  simp only [boundaryBernstein77_add]

  rw [boundaryTermCoefficient77_reconstruction (((-2116157440/59049 : ℝ))/3) ((21-21)+2*3-5) 0 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2116157440/59049 : ℝ))/36) (((21-21)+2*3-5)+1) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2116157440/59049 : ℝ))/216) (((21-21)+2*3-5)+2) 1 3 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((40487047168/4782969 : ℝ))/3) ((21-21)+2*4-5) 0 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((40487047168/4782969 : ℝ))/36) (((21-21)+2*4-5)+1) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((40487047168/4782969 : ℝ))/216) (((21-21)+2*4-5)+2) 1 4 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-60155799296/43046721 : ℝ))/3) ((21-21)+2*5-5) 0 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-60155799296/43046721 : ℝ))/36) (((21-21)+2*5-5)+1) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-60155799296/43046721 : ℝ))/216) (((21-21)+2*5-5)+2) 1 5 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((16458456017087/99179645184 : ℝ))/3) ((21-21)+2*6-5) 0 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((16458456017087/99179645184 : ℝ))/36) (((21-21)+2*6-5)+1) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((16458456017087/99179645184 : ℝ))/216) (((21-21)+2*6-5)+2) 1 6 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-3202435542593/223154201664 : ℝ))/3) ((21-21)+2*7-5) 0 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-3202435542593/223154201664 : ℝ))/36) (((21-21)+2*7-5)+1) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-3202435542593/223154201664 : ℝ))/216) (((21-21)+2*7-5)+2) 1 7 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((464622800108815/514147280633856 : ℝ))/3) ((21-21)+2*8-5) 0 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((464622800108815/514147280633856 : ℝ))/36) (((21-21)+2*8-5)+1) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((464622800108815/514147280633856 : ℝ))/216) (((21-21)+2*8-5)+2) 1 8 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-2273787291250585/55527906308456448 : ℝ))/3) ((21-21)+2*9-5) 0 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-2273787291250585/55527906308456448 : ℝ))/36) (((21-21)+2*9-5)+1) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-2273787291250585/55527906308456448 : ℝ))/216) (((21-21)+2*9-5)+2) 1 9 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((96411338058443/74037208411275264 : ℝ))/3) ((21-21)+2*10-5) 0 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((96411338058443/74037208411275264 : ℝ))/36) (((21-21)+2*10-5)+1) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((96411338058443/74037208411275264 : ℝ))/216) (((21-21)+2*10-5)+2) 1 10 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-27853481344505/999502313552216064 : ℝ))/3) ((21-21)+2*11-5) 0 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-27853481344505/999502313552216064 : ℝ))/36) (((21-21)+2*11-5)+1) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-27853481344505/999502313552216064 : ℝ))/216) (((21-21)+2*11-5)+2) 1 11 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((140944386775/374813367582081024 : ℝ))/3) ((21-21)+2*12-5) 0 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((140944386775/374813367582081024 : ℝ))/36) (((21-21)+2*12-5)+1) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((140944386775/374813367582081024 : ℝ))/216) (((21-21)+2*12-5)+2) 1 12 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-5818211165/1999004627104432128 : ℝ))/3) ((21-21)+2*13-5) 0 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-5818211165/1999004627104432128 : ℝ))/36) (((21-21)+2*13-5)+1) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-5818211165/1999004627104432128 : ℝ))/216) (((21-21)+2*13-5)+2) 1 13 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((204815881/17991041643939889152 : ℝ))/3) ((21-21)+2*14-5) 0 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((204815881/17991041643939889152 : ℝ))/36) (((21-21)+2*14-5)+1) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((204815881/17991041643939889152 : ℝ))/216) (((21-21)+2*14-5)+2) 1 14 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-255391/13493281232954916864 : ℝ))/3) ((21-21)+2*15-5) 0 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-255391/13493281232954916864 : ℝ))/36) (((21-21)+2*15-5)+1) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-255391/13493281232954916864 : ℝ))/216) (((21-21)+2*15-5)+2) 1 15 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((803/80959687397729501184 : ℝ))/3) ((21-21)+2*16-5) 0 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((803/80959687397729501184 : ℝ))/36) (((21-21)+2*16-5)+1) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((803/80959687397729501184 : ℝ))/216) (((21-21)+2*16-5)+2) 1 16 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (((-1/1457274373159131021312 : ℝ))/3) ((21-21)+2*17-5) 0 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (-((-1/1457274373159131021312 : ℝ))/36) (((21-21)+2*17-5)+1) 1 17 (by norm_num) (by norm_num),
    boundaryTermCoefficient77_reconstruction (7*((-1/1457274373159131021312 : ℝ))/216) (((21-21)+2*17-5)+2) 1 17 (by norm_num) (by norm_num)]

  dsimp only [boundaryTerm77,boundaryImHighColumn77_21,boundaryZ77]

  ring


end

end HTGeometry.ThetaRatioInfinity
