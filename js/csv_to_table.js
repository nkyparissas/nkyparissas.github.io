d3.text("uploads/score.csv", function(data) {

				  
				  var parsedCSV = d3.csv.parseRows(data);
				  var headers = [parsedCSV.shift()]
				  
				  var table = d3.select(body)
					.append(table)
				  var thead = table.append(thead)
				  var tbody = table.append(tbody)
				  var tfoot = table.append(tfoot)
					
				  thead.selectAll(tr)
					.data(headers).enter()
					.append(tr)
					.selectAll(th)
					.data(d = d).enter()
					.append(th)
					.text(d = d)

				  tbody.selectAll(tr)
					.data(parsedCSV).enter()
					.append(tr)
					.selectAll(td)
					.data(d = d).enter()
					.append(td)
					.text(d = d)
				});