resource MicroResAra = open Prelude in {

  param
    Number  = Sg | Dl | Pl ;
    Case    = Nom | Acc ; -- | Gen ;
    Gender  = Fem | Masc ;
    Tense   = Perf  | Impf ;
    Species = Hum | NoHum ;
    State   = Def | Indef ;
    -- Person = P1 | P2 | P3 ;
    
    AgreementGNSp   = AgrGNSp Gender Number Species;
    -- Agreement     = Agr Number ;

  oper

------------Nouns--------------

{- in Arabic a noun is inflected by its number and case added the State to simplify using the def and indef states
 but this is not an inflectional feature 
 - both the Gender and the Species are inherent features , the latter is only significant with the Pl -}

    Noun : Type = {s : State => Number => Case => Str ; g: Gender ; sp: Species } ;    

    mkNoun : (sg,dlNom,dlAcc,pl : Str) -> Gender -> Species -> Noun 
    = \sg,dlNom,dlAcc,pl,gen,species -> 
    { s   = table { 
        Def => table { 
          Sg => table { _ => sg };
          Dl => table {Nom  => dlNom ; Acc  => dlAcc } ;
          Pl => table { _ => pl }
          } ;
        Indef => table {
          Sg => table { _ => "ال" + sg };
          Dl => table {Nom  => "ال" + dlNom ; Acc  => "ال" + dlAcc } ;
          Pl => table { _ => "ال" + pl }  
          } 
      };
      g   = gen ;
      sp  = species ;
      } ;
-- The first two are special cases of the fem nouns
    femNoun : Str -> Gender -> Species -> Noun = \sg,gen,species -> case <sg,gen> of {
      < "نار",Fem >           => mkNoun sg (sg+"ان") (sg+"ين") ("نيران") gen species ;
      < "جعة",Fem >           => uncountable sg gen species ;
      <sub + ("ة"|"ت"),Fem> => mkNoun sg (sub+"تان") (sub+"تين") (sub+"ات") gen species ;
      _                       => uncountable sg gen species 
    } ;
-- blood and water have only Sg and Pl but no Dl  
    brokenNoun : Str -> Str -> Gender -> Species -> Noun = \sg,pl,gen,species -> case <sg,gen> of {
      <"دم",Masc>  => mkNoun sg nonExist nonExist pl gen species ;
      <"ماء",Masc> => mkNoun sg nonExist nonExist pl gen species ;
      <_,Masc>     => mkNoun sg (sg+"ان") (sg+"ين") pl gen species ;
      <_,Fem>      => mkNoun sg (sg+"تان") (sg+"تين") pl gen species
    } ;
-- Music, grammar, beer, milk and wine are uncountable nouns
    uncountable : Str -> Gender -> Species -> Noun = \sg,gen,species -> 
      mkNoun sg nonExist nonExist nonExist gen species ;

------------Verbs--------------
-- in Arabic a verb is inflected by its Tense, Gender, number and Species

    Verb : Type = {s : Tense => AgreementGNSp => Str} ;
    Verb2 : Type = Verb ** {c : Str} ;

    {- 1st and 2nd person are not used in this grammar so we'll skip them, 
     as in Arabic they have specific form and don't use infinitives 
    (infinitives in Arabic is a noun actually) -}
    mkVerb : (y,z,g,h,i,j,w,x,q,r,s,t : Str) -> Verb
      = \y,z,g,h,i,j,w,x,q,r,s,t -> {
      s = table { 
        Perf => table {
          AgrGNSp Masc Sg _  => y ;
          AgrGNSp Fem Sg _   => z ;
          AgrGNSp _ Pl NoHum => z ;
          -- AgrTGNSP Perf _ Sg Hum P1 => a
          -- AgrTGNSP Perf _ (Dl|Pl) _ P1 => b
          -- AgrTGNSP Perf _ Sg _ P2 => c
          -- AgrTGNSP Perf _ Dl _ P2 => d
          -- AgrTGNSP Perf Masc Pl _ P2 => e
          -- AgrTGNSP Perf Fem Pl _ P2 => f
          AgrGNSp Masc Dl _  => g ;
          AgrGNSp Fem Dl _   => h ;
          AgrGNSp Masc Pl _  => i ;
          AgrGNSp Fem Pl _   => j 
        } ;
        Impf => table {
          AgrGNSp Masc Sg _  => w ;
          AgrGNSp Fem Sg _   => x ;
          AgrGNSp _ Pl NoHum => x ;      
          -- AgrTGNSP impf _ Sg Hum P1 => k
          -- AgrTGNSP impf _ (Dl|Pl) _ P1 => l
          -- AgrTGNSP impf _ Sg _ P2 => m
          -- AgrTGNSP impf _ Dl _ P2 => n
          -- AgrTGNSP impf Masc Pl _ P2 => o
          -- AgrTGNSP impf Fem Pl _ P2 => p
          AgrGNSp Masc Dl _  => q ;
          AgrGNSp Fem Dl _   => r ;
          AgrGNSp Masc Pl Hum=> s ;
          AgrGNSp Fem Pl Hum => t 
        } 
      }
    } ;
    
-- regular verbs with predictable variations
    regVerb : (past: Str) -> Verb = \past -> 
      mkVerb past (past + "ت") (past + "ا") (past + "تا") (past + "وا") (past + "ن") 
      ("ي" + past) ("ت" + past) ("ي" + past + "ان") ("ت" + past + "ان") ("ي" + past + "ون") ("ي" + past + "ن") ;

    
    specialVerb : Str -> Str -> Str -> Verb = \past,presSub,femPlRoot -> case past of {
      "أ" + sub => mkVerb past (past + "ت") (past + "ا") (past + "تا") (past + "وا") ("أ" + femPlRoot) 
        (presSub) ("ت" + presSub) ("ي" + presSub + "ان") ("ت" + presSub + "ان") ("ي" + presSub + "ون") ("ي" + femPlRoot) ;
      _         => mkVerb past (past + "ت") (past + "ا") (past + "تا") (past + "وا") femPlRoot 
        ("ي" + presSub) ("ت" + presSub) ("ي" + presSub + "ان") ("ت" + presSub + "ان") ("ي" + presSub + "ون") ("ي" + femPlRoot) 
    };

-- weak verbs has vowels at the end or inside them are treated differently
    weakVerb : (past : Str) -> Verb = \past -> case past of {
      "ا" + shtr + "ى" => mkVerb past ("ا" + shtr + "ت") ("ا" + shtr + "يا") ("ا" + shtr + "تا") ("ا" + shtr + "وا") ("ا" + shtr + "ين") 
        ("ي" + shtr + "ي") ("ت" + shtr + "ي") ("ي" + shtr + "يان") ("ت" + shtr + "يان") ("ي" + shtr + "ون") ("ي" + shtr + "ين") ;

      "ا" + ntathar    => mkVerb past ("ا" + ntathar + "ت") ("ا" + ntathar + "ا") ("ا" + ntathar + "تا") ("ا" + ntathar + "وا") ("ا" + ntathar + "ن") 
        ("ي" + ntathar) ("ت" + ntathar) ("ي" + ntathar + "ان") ("ت" + ntathar + "ان") ("ي" + ntathar + "ون") ("ي" + ntathar + "ن") ;

      j + "اء"         => mkVerb past (past + "ت") (past + "ا") (past + "تا") (j + "اؤوا") (j + "ئن")
        ("ي" + j + "يء") ("ت" + j + "يء") ("ي" + j + "يئان") ("ت" + j + "يئان") ("ي" + j + "يؤون") ("ي" + j + "ئن") ;
      
      r + "أى"         => mkVerb past (past + "ت") (past + "يا") (past + "تا") (r + "ؤوا") (r + "أين")
        ("ي" + r + "ى") ("ت" + r + "ى") ("ي" + r + "يان") ("ت" + r + "يان") ("ي" + r + "ون") ("ي" + r + "ين") ;
      
      mash + "ى"       => mkVerb past (past + "ت") (past + "يا") (past + "تا") (mash + "وا") (mash + "ين")
        ("ي" + mash + "ي") ("ت" + mash + "ي") ("ي" + mash + "يان") ("ت" + mash + "يان") ("ي" + mash + "ون") ("ي" + mash + "ين") ;
      
      "و" + jd         => mkVerb past (past + "ت") (past + "ا") (past + "تا") (past + "وا") (past + "ن") 
        ("ي" + jd) ("ت" + jd) ("ي" + jd + "ان") ("ت" + jd + "ان") ("ي" + jd + "ون") ("ي" + jd + "ن") ;

      _                => regVerb past
      
      } ;

-- in Arabic we have no copula in the present tense. 
    be_Verb : Verb = mkVerb "كان" "كانت" "كانا" "كانتا" "كانوا" "كن" "" "" "" "" "" "" ;

------------Adjs---------------
{- in Arabic an adj is inflected by its Gender, number, Species and case added the State to simplify using the def and indef states
 but this is not an inflectional feature itself. -}

    Adjective : Type = {s : State => AgreementGNSp => Case => Str} ;

    mkAinit : (ms,multi,mdn,mda,fdn,fda,mhpn,mhpa,fhp : Str) -> Adjective 
    = \ms,multi,mdn,mda,fdn,fda,mhpn,mhpa,fhp -> {
      s = table { 
        Indef   => table {
          AgrGNSp Masc Sg _   => table { _   => ms    } ;
          AgrGNSp Fem Sg _    => table { _   => multi } ;
          AgrGNSp _ Pl NoHum  => table { _   => multi } ;
          AgrGNSp Masc Dl _   => table { Nom => mdn  ; Acc => mda  } ;
          AgrGNSp Fem Dl _    => table { Nom => fdn  ; Acc => fda  } ;
          AgrGNSp Masc Pl Hum => table { Nom => mhpn ; Acc => mhpa };
          AgrGNSp Fem Pl Hum  => table { _   => fhp   }
        };
        Def => table {
          AgrGNSp Masc Sg _   => table { _   => "ال" + ms    } ;
          AgrGNSp Fem Sg _    => table { _   => "ال" + multi } ;
          AgrGNSp _ Pl NoHum  => table { _   => "ال" + multi } ;
          AgrGNSp Masc Dl _   => table { Nom => "ال" + mdn  ; Acc => "ال" + mda  } ;
          AgrGNSp Fem Dl _    => table { Nom => "ال" + fdn  ; Acc => "ال" + fda  } ; 
          AgrGNSp Masc Pl Hum => table { Nom => "ال" + mhpn ; Acc => "ال" + mhpa } ; 
          AgrGNSp Fem Pl Hum  => table { _   => "ال" + fhp }
        }
      }  
    } ;   

{- some adjective has more than one form like "قديم" in Pl: "قدام" "قدامى" "قدماء",
  it was very tricky and confusing as it depends on the noun and the context in general-}
    mkAdj : Str -> Adjective
      = \ms -> case ms of {
        -- pre "أ" => red + "اء"
        "أ" + sub     => mkAinit ms (sub + "اء") (sub + "اوان") (sub + "اوين") (sub + "اوتان") (sub + "اوتين") sub sub (sub + "اوات") ;
        "قديم"        => mkAinit ms (ms + "ة") (ms + "ان") (ms + "ين") (ms + "تان") (ms + "تين") ("قدماء") ("قدماء") (ms + "ات") ;
        kab + "ي" + r => mkAinit ms (ms + "ة") (ms + "ان") (ms + "ين") (ms + "تان") (ms + "تين") (kab + "ا" + r) (kab + "ا" + r) (ms + "ات") ;
        saye + "ء"    => mkAinit ms (saye + "ئة") (saye + "ئان") (saye + "ئين") (saye + "ئتان") (saye + "ئتين") (saye + "ئون") (saye + "ئين") (saye + "ئات") ;
        _             => mkAinit ms (ms + "ة") (ms + "ان") (ms + "ين") (ms + "تان") (ms + "تين") (ms + "ون") (ms + "ين") (ms + "ات")  --ToDo
    };


}