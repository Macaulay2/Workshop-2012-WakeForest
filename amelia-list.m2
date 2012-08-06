f = (L) -> (
     if #L === 0 then return {{}};
     a := L#0;
     L = drop(L,1);
     flatten for i from 0 to a-1 list (
	  M := f L;
	  M/(m -> prepend(i,m))
	  )
     )

end

restart
load "amelia-list.m2"
 L = {2,3,1}

f {}
f{3}
f{3,2}
f L
